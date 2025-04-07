#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <time.h>
#include <unistd.h>   
#include <sys/wait.h> 

#define MAX_USERS 5
#define MAX_SLOTS 3 // parking slots available (can change if necessary)
#define MAX_RESOURCES 3
#define MAX_ESSENTIALS 6
#define MAX_BOOKINGS 5000

// Test time defintion
#define TEST_START_DAY 10
#define TEST_START_MONTH 5
#define TEST_START_YEAR 2025
#define TEST_DAYS 10

// Status definition
#define STATUS_PENDING 0
#define STATUS_ACCEPTED 1
#define STATUS_REJECTED 2

// Essential definition
#define PAIR_COUNT 3
#define MAX_STRING_LENGTH 20

typedef struct Member {
    char name[MAX_STRING_LENGTH];
} Member;

Member members[MAX_USERS] = {
    {"member_A"},
    {"member_B"},
    {"member_C"},
    {"member_D"},
    {"member_E"}
};

typedef struct Booking {
    char member[MAX_STRING_LENGTH];
    int parking_slot;
    char date[11]; // YYYY-MM-DD
    char time[6]; // hh:mm
    float duration;
    char essentials[3][20]; // 3 pairs
    int essential_count;
    int status; // 0 = pending, 1 = accepted, 2 = rejected
    time_t start_time; //?
    time_t end_time;
    char type[12];
} Booking;

typedef struct BookingList {
    Booking* bookings;       // array of all bookigns
    int booking_count;       // total number of bookings
    int capacity;            // capacity of the array
} BookingList;

// Global structure to hold scheduler results for the analyzer
typedef struct SchedulerResults {
    int* accepted_idx;      // array of indices of accepted bookings
    int accepted_count;     // count of accepted bookings
    int* rejected_idx;      // array of indices of rejected bookings
    int rejected_count;     // count of rejected bookings
    int total_received;     // total number of bookings received
} SchedulerResults;

typedef struct SystemResources {
    int parking_slots[MAX_SLOTS];  // use to check if parcking slot is occupied
    int battery;
    int cable;
    int locker;
    int umbrella;
    int valet;
    int inflation;
} SystemResources;

SystemResources sys_res = {
    .parking_slots = {0},
    .battery = MAX_RESOURCES,
    .cable = MAX_RESOURCES,
    .locker = MAX_RESOURCES,
    .umbrella = MAX_RESOURCES,
    .valet = MAX_RESOURCES,
    .inflation = MAX_RESOURCES
};

// Map essentials pairs
static const char* essential_pairs[PAIR_COUNT][2] = {
    {"battery", "cable"},
    {"locker", "umbrella"},
    {"inflationservice", "valetpark"}
};

void FCFS_Scheduler(Booking* bookings, int numBookings, int* rejectList, int* rejectCounter);
void Priority_Scheduler(Booking* bookings, int numBookings, int* rejectList, int* rejectCounter);
void command_processor(char *cmd);
static bool time_overlap(Booking* booking1, Booking* booking2);
static int check_parking_conflict(Booking* item, Booking* bookings, int* acceptList, int acceptCount);
static int check_essential_conflict(Booking* item, Booking* bookings, int* acceptList, int acceptCount);

// Return priority level
static int get_priority_level(const char *type) {
    if (strcmp(type, "Event") == 0) return 3;
    if (strcmp(type, "Reservation") == 0) return 2;
    if (strcmp(type, "Parking") == 0) return 1;
    return 0;
}

// Compare priority level of two bookings
int comparePriority(const void* a, const void* b) {
    Booking* bookingA = (Booking*)a;
    Booking* bookingB = (Booking*)b;
    return get_priority_level(bookingB->type) - get_priority_level(bookingA->type);
}

// Initialize and allocate memory to booking list
void init_booking_list(BookingList* list, int size) {
    list->bookings = malloc(size * sizeof(Booking));
    list->booking_count = 0;
    list->capacity = size;
}

// Global variables for parent to hold all sent bookings
static BookingList allBookings;
// Global variables for each scheduler (e.g., FCFS and Priority)
SchedulerResults fcfs_results = {NULL, 0, NULL, 0, 0};
SchedulerResults prio_results = {NULL, 0, NULL, 0, 0};
// Global variable to track invalid commands
int invalid_command_count = 0;

// Tool function
static void to_lower_case(char *str) {
    for (int i = 0; str[i]; i++) {
        str[i] = (char)tolower((unsigned char)str[i]);
    }
}

static bool validate_datetime(const char *date, const char *time) {
    if (strlen(date) != 10 || date[4] != '-' || date[7] != '-') return false;
    if (strlen(time) != 5 || time[2] != ':') return false;

    int year, month, day, hour, minute;
    if (sscanf(date, "%d-%d-%d", &year, &month, &day) != 3) return false;
    if (sscanf(time, "%d:%d", &hour, &minute) != 2) return false;

    return (hour >= 0 && hour <= 23 && minute >= 0 && minute <= 59);
}

static time_t convert_to_time_t(const char* date, const char* time) {
    struct tm tm = {0};
    sscanf(date, "%d-%d-%d", &tm.tm_year, &tm.tm_mon, &tm.tm_mday);
    sscanf(time, "%d:%d", &tm.tm_hour, &tm.tm_min);
   
    tm.tm_year -= 1900;
    tm.tm_mon -= 1;
   
    return mktime(&tm);
}

// Resource management function
static const char* get_pair_essential(const char *essential) {
    char lower_essential[MAX_STRING_LENGTH];
    strncpy(lower_essential, essential, sizeof(lower_essential)-1);
    lower_essential[sizeof(lower_essential)-1] = '\0';
    to_lower_case(lower_essential);

    size_t i;
    for (int i = 0; i < PAIR_COUNT; i++) {
        if (strcmp(lower_essential, essential_pairs[i][0]) == 0) return essential_pairs[i][1];
        if (strcmp(lower_essential, essential_pairs[i][1]) == 0) return essential_pairs[i][0];
    }
    return NULL;
}


/* Scheduler Module Functions */

// Check if bookings involving essentials have conflict (0 -> no conflict, -1 -> has conflict)
static int check_essential_conflict(Booking* item, Booking* bookings, int* acceptList, int acceptCount){
    // Check essentials for conflict  
    if (item->essential_count > 0) {
        // 1. Validate all pairs first
        for (int e = 0; e < item->essential_count; e++) {
            const char* pair = get_pair_essential(item->essentials[e]);
            if (!pair) return -1; // Invalid essential
        }
       
        // 2. Check conflicts with existing bookings
        for (int e = 0; e < item->essential_count; e++) {
            const char* essential = item->essentials[e];

            int total_usage = 0;
    
            // Count usage of the essential in accepted bookings
            for (int i = 0; i < acceptCount; i++) {
                Booking* acceptedBooking = &bookings[acceptList[i]];
                if (!time_overlap(item, acceptedBooking)) continue;

                for (int j = 0; j < acceptedBooking->essential_count; j++) {
                    if (strcmp(acceptedBooking->essentials[j], essential) == 0) {
                        total_usage++;
                    }
                }
            }

            // Check if total usage exceeds the limit
            if (total_usage >= MAX_RESOURCES) {
                return -1; // Essential conflict
            }
        }
    }

    return 0;
}

// Check if the booking of parking has any conflict with accepted bookings
// (0-N -> no conflict, indicate first avail parking slot, -1 -> has conflict)
static int check_parking_conflict(Booking* item, Booking* bookings, int* acceptList, int acceptCount) {
    // Check parking for conflict
    int available_slots[MAX_SLOTS] = {1, 1, 1};

    for (int i = 0; i < acceptCount; i++) {
        int acceptedIndex = acceptList[i];
        Booking* acceptedBooking = &bookings[acceptedIndex];

        // Check if the accepted booking overlaps in time with the current booking
        if (time_overlap(item, acceptedBooking)) {
            // If there is a time overlap, mark the parking slot as unavailable
            if (acceptedBooking->parking_slot >= 0 && acceptedBooking->parking_slot < MAX_SLOTS) {
                available_slots[acceptedBooking->parking_slot] = 0;
            }
        }
    }

    // If the booking already has a valid parking slot, check if it is still available
    if (item->parking_slot >= 0 && item->parking_slot < MAX_SLOTS) {
        if (available_slots[item->parking_slot]) {
            return item->parking_slot; // Keep the current slot if available
        }
    }

    // Assign the first available parking slot
    for (int j = 0; j < MAX_SLOTS; j++) {
        if (available_slots[j] == 1) {
            return j;
        }
    }

    return -1; // No parking available
}

static bool has_time_conflict(Booking* item, Booking* bookings, int* acceptList, int acceptCount) {
    if (strcmp(item->type, "*") == 0) {
        // check essential conflict
        return (check_essential_conflict(item, bookings, acceptList, acceptCount) == -1);
    } else {
        // check slot conflict
        bool parking_conflict = (check_parking_conflict(item, bookings, acceptList, acceptCount) == -1);
        bool essential_conflict = (check_essential_conflict(item, bookings, acceptList, acceptCount) == -1);    
        return parking_conflict || essential_conflict;
    }
}

// Cancel the bookings and release resources
void cancelBooking(Booking* booking) {
    booking->status = STATUS_REJECTED;
    booking->parking_slot = -1;
}

static void create_booking(const char* member, const char* date, const char* time, float duration, char essentials[][MAX_STRING_LENGTH], int count, int slot, const char* type) {
    if(duration == 0) {
        printf("Error: Booking duration can't be 0, must be atleast 1 hour\n");
        invalid_command_count++;
        return;
    }

    Booking new_booking = {
        .parking_slot = slot,
        .status = STATUS_PENDING,
        .start_time = convert_to_time_t(date, time),
        .end_time = convert_to_time_t(date, time) + (time_t)(duration * 3600),
        .essential_count = count,
        .duration = duration
    };

    strncpy(new_booking.member, member, MAX_STRING_LENGTH-1);
    strncpy(new_booking.date, date, sizeof(new_booking.date)-1);
    strncpy(new_booking.time, time, sizeof(new_booking.time)-1);
    strncpy(new_booking.type, type, sizeof(new_booking.type)-1);

    for (int i = 0; i < count; i++) {
        strncpy(new_booking.essentials[i], essentials[i], MAX_STRING_LENGTH-1);
    }

    allBookings.bookings[allBookings.booking_count++] = new_booking;
}

static bool time_overlap(Booking* booking1, Booking* booking2) {
    // Check if the dates are the same
    if (strcmp(booking1->date, booking2->date) != 0) return false; // Different dates, no overlap

    // Check if the time intervals overlap
    return (booking1->start_time < booking2->end_time && booking2->start_time < booking1->end_time);
}

// FCFS Algirhtm Function
void FCFS_Scheduler(Booking* bookings, int numBookings, int* acceptList, int* acceptCounter) {
    for (int i = 0; i < numBookings; i++) {
        if (bookings[i].status != STATUS_PENDING) continue;

        // Only non-" *" types need to be allocated parking Spaces
        if (strcmp(bookings[i].type, "*") != 0) {
            if (bookings[i].parking_slot == -1) {
                bookings[i].parking_slot = check_parking_conflict(&bookings[i], bookings, acceptList, *acceptCounter);
            }
            // Refuse when the parking space is invalid
            if (bookings[i].parking_slot == -1) {
                cancelBooking(&bookings[i]);
                continue;
            }
        }

        // Checking for conflict
        if (!has_time_conflict(&bookings[i], bookings, acceptList, *acceptCounter)) {
            bookings[i].status = STATUS_ACCEPTED;
            acceptList[(*acceptCounter)++] = i;
        } else {
            cancelBooking(&bookings[i]);
        }
    }
}

//Priority Algorithm Function
void Priority_Scheduler(Booking* bookings, int numBookings, int* acceptList, int* acceptCounter) {

    for (int i = 0; i < numBookings; i++) {
        // Process only pending bookings
        if (bookings[i].status != STATUS_PENDING) continue;

        // Debug: Print booking details and priority
        int priority = get_priority_level(bookings[i].type);

        bool canAccept = !has_time_conflict(&bookings[i], bookings, acceptList, *acceptCounter);

        // Accept or reject the booking
        if (canAccept) {
            bookings[i].status = STATUS_ACCEPTED;
            acceptList[(*acceptCounter)++] = i;
            if(strcmp(bookings[i].type, "*") != 0) {
                bookings[i].parking_slot = check_parking_conflict(&bookings[i], bookings, acceptList, *acceptCounter);
            }
        } 
        
        else {
            // Check if the booking can replace a lower-priority booking
            int lowestPriorityIndex = -1;
            int currPriority = priority;

            for (int j = *acceptCounter - 1; j >= 0; j--) { // Iterate from the back
                int acceptedIndex = acceptList[j]; // access accepted indexes from accept list
                if(!time_overlap(&bookings[i], &bookings[acceptedIndex])) continue;

                int acceptedPriority = get_priority_level(bookings[acceptedIndex].type);
                // detect & store first detected lower priority
                if (acceptedPriority < currPriority) {
                    // currPriority = acceptedPriority;
                    lowestPriorityIndex = j;
                }
            }

            if (lowestPriorityIndex != -1) { // found a lower priority
                // Replace the lowest-priority booking
                int replacedIndex = acceptList[lowestPriorityIndex];

                bookings[i].parking_slot = bookings[replacedIndex].parking_slot;
                bookings[i].status = STATUS_ACCEPTED;
                cancelBooking(&bookings[replacedIndex]);

                acceptList[lowestPriorityIndex] = i;
            }
            else {
                cancelBooking(&bookings[i]);
            }
        }
    }
}

/* Input Module Functions */
//functions for adding bookings
void add_parking(char *member, char *date, char *time, float duration, char essentials[][MAX_STRING_LENGTH], int count) {
    if (!validate_datetime(date, time)) {
        printf("Error: Invalid date/time format\n");
        invalid_command_count++;
        return;
    }

    create_booking(member, date, time, duration, essentials, count, -1, "Parking");
    printf("-> [Pending]");
}

void add_reservation(char *member, char *date, char *time, float duration, char essentials[][MAX_STRING_LENGTH], int count) {
    if (!validate_datetime(date, time)) {
        printf("Invalid date/time format\n");
        invalid_command_count++;
        return;
    }

    create_booking(member, date, time, duration, essentials, count, -1, "Reservation");
    printf("-> [Pending]");
}

void book_essentials(char *member, char *date, char *time, float duration, char essentials[][MAX_STRING_LENGTH], int count) {
    if (!validate_datetime(date, time)) {
        printf("Invalid date/time format\n");
        invalid_command_count++;
        return;
    }

    create_booking(member, date, time, duration, essentials, count, -1, "*");
    printf("-> [Pending]");
}

void add_event(char *member, char *date, char *time, float duration, char essentials[][MAX_STRING_LENGTH], int count) {
    if (!validate_datetime(date, time)) {
        printf("Invalid date/time format\n");
        invalid_command_count++;
        return;
    }

    create_booking(member, date, time, duration, essentials, count, -1, "Event");
    printf("-> [Pending]");
   
}


void process_batch_file(const char *filename) {
    FILE *file = fopen(filename, "r");
    if (!file) {
        perror("Unable to open batch file");
        invalid_command_count++;
        return;
    }

    char line[256];
    while (fgets(line, sizeof(line), file)) {
        line[strcspn(line, "\n")] = 0; // Remove a newline
        command_processor(line);
    }

    fclose(file);
}

static Member* get_member(const char* member_name) {
    char clean_name[MAX_STRING_LENGTH];
    strncpy(clean_name, member_name, sizeof(clean_name)-1);
    clean_name[sizeof(clean_name)-1] = '\0';
   
    // Remove the dash
    if (clean_name[0] == '-') {
        size_t len = strlen(clean_name);
        memmove(clean_name, clean_name + 1, len);
    }
   
    for (int i = 0; i < MAX_USERS; i++) {
        if (strcmp(clean_name, members[i].name) == 0) {
            return &members[i];
        }
    }
    return NULL;
}

void command_processor(char *cmd) {
    char *token = strtok(cmd, " ");
    if (token == NULL) return;

    if (strcmp(token, "addParking") == 0) {
        char member_name[MAX_STRING_LENGTH], date[11], time[6];
        float duration;
        char essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH];
        int count = 0;
       
        token = strtok(NULL, " ");
        if (token) strcpy(member_name, token);
        token = strtok(NULL, " ");
        if (token) strcpy(date, token);
        token = strtok(NULL, " ");
        if (token) strcpy(time, token);
        token = strtok(NULL, " ");
        if (token) duration = (float)atof(token);
       
        while ((token = strtok(NULL, " ")) != NULL && count < MAX_ESSENTIALS) {
            if (token[strlen(token) - 1] == ';')
                token[strlen(token) - 1] = '\0';
            strcpy(essentials[count++], token);
        }

        Member* member = get_member(member_name);
        if (!member) {
            printf("Error: Invalid member name\n");
            invalid_command_count++;
            return;
        }
        add_parking(member->name, date, time, duration, essentials, count);
    }
    else if (strcmp(token, "addReservation") == 0) {
        char member_name[MAX_STRING_LENGTH], date[11], time[6];
        float duration;
        char essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH];
        int count = 0;

        token = strtok(NULL, " ");
        if (token) strcpy(member_name, token);
        token = strtok(NULL, " ");
        if (token) strcpy(date, token);
        token = strtok(NULL, " ");
        if (token) strcpy(time, token);
        token = strtok(NULL, " ");
        if (token) duration = (float)atof(token);
       
        while ((token = strtok(NULL, " ")) != NULL && count < MAX_ESSENTIALS) {
            if (token[strlen(token) - 1] == ';')
                token[strlen(token) - 1] = '\0';
            strcpy(essentials[count++], token);
        }

        Member* member = get_member(member_name);
        if (!member) {
            printf("Error: Invalid member name\n");
            invalid_command_count++;
            return;
        }
        add_reservation(member->name, date, time, duration, essentials, count);
    }
    else if (strcmp(token, "bookEssentials") == 0) {
        char member_name[MAX_STRING_LENGTH], date[11], time[6];
        float duration;
        char essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH];
        int count = 0;

        token = strtok(NULL, " ");
        if (token) strcpy(member_name, token);
        token = strtok(NULL, " ");
        if (token) strcpy(date, token);
        token = strtok(NULL, " ");
        if (token) strcpy(time, token);
        token = strtok(NULL, " ");
        if (token) duration = (float)atof(token);
       
        while ((token = strtok(NULL, " ")) != NULL && count < MAX_ESSENTIALS) {
            if (token[strlen(token) - 1] == ';')
                token[strlen(token) - 1] = '\0';
            strcpy(essentials[count++], token);
        }

        Member* member = get_member(member_name);
        if (!member) {
            printf("Error: Invalid member name\n");
            invalid_command_count++;
            return;
        }
        book_essentials(member->name, date, time, duration, essentials, count);
    }
    else if (strcmp(token, "addEvent") == 0) {
        char member_name[MAX_STRING_LENGTH], date[11], time[6];
        float duration;
        char essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH];
        int count = 0;

        token = strtok(NULL, " ");
        if (token) strcpy(member_name, token);
        token = strtok(NULL, " ");
        if (token) strcpy(date, token);
        token = strtok(NULL, " ");
        if (token) strcpy(time, token);
        token = strtok(NULL, " ");
        if (token) duration = (float)atof(token);
       
        while ((token = strtok(NULL, " ")) != NULL && count < MAX_ESSENTIALS) {
            if (token[strlen(token) - 1] == ';')
                token[strlen(token) - 1] = '\0';
            strcpy(essentials[count++], token);
        }

        Member* member = get_member(member_name);
        if (!member) {
            printf("Error: Invalid member name\n");
            invalid_command_count++;
            return;
        }
        add_event(member->name, date, time, duration, essentials, count);
    }
}


/* Output Module */
// Print all bookings
static void print_bookings(Booking* bookings, int booking_count, int* acceptList, int acceptCounter, char *algorithms) {
    FILE *fp = fopen("SPMS_Report_G34.txt", "a");
    if (!fp) {
        perror("Failed to open report file");
        return;
    }
    
    // Create tracking array for accepted bookings
    bool* is_accepted = calloc(booking_count, sizeof(bool));
    for (int i = 0; i < acceptCounter; i++) {
        if (acceptList[i] < booking_count) {
            is_accepted[acceptList[i]] = true;
        }
    }

    // Print ACCEPTED bookings
    fprintf(fp, "\n*** ACCEPTED Bookings - %s ***\n", algorithms);
    for (int i = 0; i < MAX_USERS; i++) {
        bool has_accepted = false;

        // Check if member has any accepted bookings
        for (int j = 0; j < acceptCounter; j++) {
            int idx = acceptList[j];
            if (idx < booking_count && strcmp(bookings[idx].member, members[i].name) == 0) {
                has_accepted = true;
                break;
            }
        }

        if (has_accepted) {
            fprintf(fp, "\n%s has the following ACCEPTED bookings:\n", members[i].name);
            fprintf(fp, "Date        Start  End    Type           Device\n");
            fprintf(fp, "===========================================================================\n");

            for (int j = 0; j < acceptCounter; j++) {
                int idx = acceptList[j];
                if (idx >= booking_count) continue;

                Booking *b = &bookings[idx];
                if (strcmp(b->member, members[i].name) == 0) {
                    // Calculate end time
                    char end_time[6];
                    int start_hour, start_minute;
                    sscanf(b->time, "%d:%d", &start_hour, &start_minute);
                    int end_hour = start_hour + (int)b->duration;
                    int end_minute = start_minute + (int)((b->duration - (int)b->duration) * 60);
                    if (end_minute >= 60) {
                        end_hour += end_minute / 60;
                        end_minute %= 60;
                    }
                    sprintf(end_time, "%02d:%02d", end_hour, end_minute);

                    // Print booking details
                    fprintf(fp, "%s  %s  %s  %-14s", b->date, b->time, end_time, b->type);

                    if (b->essential_count > 0) {
                        char processed_essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH] = {0};
                        int processed_count = 0;
                    
                        for (int k = 0; k < b->essential_count; k++) {  
                            char current_essential[MAX_STRING_LENGTH];
                            strncpy(current_essential, b->essentials[k], MAX_STRING_LENGTH - 1);
                            current_essential[MAX_STRING_LENGTH - 1] = '\0';
                            to_lower_case(current_essential);
                    
                            // check whether processed the device
                            bool processed = false;
                            for (int p = 0; p < processed_count; p++) {
                                if (strcmp(current_essential, processed_essentials[p]) == 0) {
                                    processed = true;
                                    break;
                                }
                                const char* pair = get_pair_essential(current_essential);
                                if (pair && strcmp(pair, processed_essentials[p]) == 0) {
                                    processed = true;
                                    break;
                                }
                            }
                    
                            if (processed) {
                                continue;
                            }
                    
                            // process the current and its pair
                            const char* pair = get_pair_essential(current_essential);
                            fprintf(fp, " %s", b->essentials[k]); 
                            if (pair) {
                                fprintf(fp, "\n                                         %s", pair);
                                strncpy(processed_essentials[processed_count], pair, MAX_STRING_LENGTH - 1);
                                processed_count++;
                            }
                            // add to processed array
                            strncpy(processed_essentials[processed_count], current_essential, MAX_STRING_LENGTH - 1);
                            processed_count++;
                        }
                    } else {
                        fprintf(fp, " *");
                    }
                    fprintf(fp, "\n");
                }
            }
        }
    }

    // Print REJECTED bookings
    fprintf(fp, "\n*** REJECTED Bookings - %s ***\n", algorithms);
    for (int i = 0; i < MAX_USERS; i++) {
        bool has_rejected = false;

        // Check if member has any rejected bookings
        for (int j = 0; j < booking_count; j++) {
            if (!is_accepted[j] && strcmp(bookings[j].member, members[i].name) == 0) {
                has_rejected = true;
                break;
            }
        }

        if (has_rejected) {
            fprintf(fp, "\n%s has the following REJECTED bookings:\n", members[i].name);
            fprintf(fp, "Date        Start  End    Type           Device\n");
            fprintf(fp, "===========================================================================\n");

            for (int j = 0; j < booking_count; j++) {
                if (!is_accepted[j] && strcmp(bookings[j].member, members[i].name) == 0) {
                    Booking *b = &bookings[j];
                   
                    // Calculate end time
                    char end_time[6];
                    int start_hour, start_minute;
                    sscanf(b->time, "%d:%d", &start_hour, &start_minute);
                    int end_hour = start_hour + (int)b->duration;
                    int end_minute = start_minute + (int)((b->duration - (int)b->duration) * 60);
                    if (end_minute >= 60) {
                        end_hour += end_minute / 60;
                        end_minute %= 60;
                    }
                    sprintf(end_time, "%02d:%02d", end_hour, end_minute);

                    // Print booking details
                    fprintf(fp, "%s  %s  %s  %-14s", b->date, b->time, end_time, b->type);

                    if (b->essential_count > 0) {
                        char processed_essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH] = {0};
                        int processed_count = 0;
                    
                        for (int k = 0; k < b->essential_count; k++) {  
                            char current_essential[MAX_STRING_LENGTH];
                            strncpy(current_essential, b->essentials[k], MAX_STRING_LENGTH - 1);
                            current_essential[MAX_STRING_LENGTH - 1] = '\0';
                            to_lower_case(current_essential);
                            bool processed = false;
                            for (int p = 0; p < processed_count; p++) {
                                if (strcmp(current_essential, processed_essentials[p]) == 0) {
                                    processed = true;
                                    break;
                                }
                                const char* pair = get_pair_essential(current_essential);
                                if (pair && strcmp(pair, processed_essentials[p]) == 0) {
                                    processed = true;
                                    break;
                                }
                            }
                    
                            if (processed) {
                                continue;
                            }
                    
                            // process the current device and pair
                            const char* pair = get_pair_essential(current_essential);
                            fprintf(fp, " %s", b->essentials[k]); 
                            if (pair) {
                                fprintf(fp, "\n                                         %s", pair);
                                // add to processed array
                                strncpy(processed_essentials[processed_count], pair, MAX_STRING_LENGTH - 1);
                                processed_count++;
                            }
                            strncpy(processed_essentials[processed_count], current_essential, MAX_STRING_LENGTH - 1);
                            processed_count++;
                        }
                    } else {
                        fprintf(fp, " *");
                    }
                    fprintf(fp, "\n");
                }
            }
        }
    }


    free(is_accepted);
    fprintf(fp, "\n- End -\n");
    fprintf(fp, "===========================================================================\n");
    fclose(fp);
}

/* Analyzer Module Functions */
static int calculate_days_between(const char* start_date, const char* end_date) {
    struct tm start_tm = {0}, end_tm = {0};
    sscanf(start_date, "%d-%d-%d", &start_tm.tm_year, &start_tm.tm_mon, &start_tm.tm_mday);
    sscanf(end_date, "%d-%d-%d", &end_tm.tm_year, &end_tm.tm_mon, &end_tm.tm_mday);

    start_tm.tm_year -= 1900;
    end_tm.tm_year -= 1900;
    start_tm.tm_mon -= 1;
    end_tm.tm_mon -= 1;

    time_t start_time = mktime(&start_tm);
    time_t end_time = mktime(&end_tm);

    return (int)difftime(end_time, start_time) / (60 * 60 * 24) + 1;
}

int main() {
    FILE *fp = fopen("SPMS_Report_G34.txt", "w");
    if (fp) fclose(fp);

    printf("~~ WELCOME TO PolyU ~~\n");
    init_booking_list(&allBookings, MAX_BOOKINGS);
   
    // Create 4 pipes, a pair for each child
    int ptoc_fd[3][2]; // parent to child
    int ctop_fd[3][2]; // child to parent
   
    for (int i = 0; i < 3; i++) { // loop for 4 process
        // Pipe Setup
        if (pipe(ptoc_fd[i]) < 0) {
            fprintf(stderr, "Error: PTOC pipe creation failed.\n");
            exit(1);
        }

        if (pipe(ctop_fd[i]) < 0) {
            fprintf(stderr, "Error: CTOP pipe creation failed.\n");
            exit(1);
        }
    }

    for (int i = 0; i < 3; i++) {
        int pid = fork();
        if (pid < 0) { // error occurred
            fprintf(stderr, "Error: Fork failed.\n");
            exit(1);
        }
       
        else if (pid == 0) { // Child Process
            // Child write to parent
            close(ptoc_fd[i][1]);
            close(ctop_fd[i][0]);

            /* Scheduling Module - Child Process*/
            if(i == 0) {
                // char buf[256];
                char msg[6] = {0}; // message passed from child to parent
                char s_request[5000] = {0}; // to store scheduling request send over from parent

                // Initialize signal protocol -> ensure all child's start before any booking starts
                if (read(ptoc_fd[i][0], msg, 5) > 0 && strcmp(msg, "START") == 0){ //receive "START"
                    write(ctop_fd[i][1], "READY", 5); // write "ready" to parent
                }

                // Allocate a accept list
                int* acceptList = (int*)calloc(2500, sizeof(int));
                if (acceptList == NULL) {
                    fprintf(stderr, "Failed to allocate memory.\n");
                    exit(1);
                }

                memset(s_request, 0, sizeof(s_request)); // clear
                int user = 0;
                char schedule = '0';
               
                while (1) {
                    char algorithm[6] = {0};

                    int bytes_read = read(ptoc_fd[0][0], algorithm, 6);
                    if (bytes_read <= 0 || strcmp(algorithm, "EXIT") == 0) {
                        break; // Exit the loop and terminate the child process
                    }
                    
                    write(ctop_fd[0][1], "ACK_ALGO", 9);
                   
                    // Receive pending bookings count
                    int pending_count;
                    read(ptoc_fd[0][0], &pending_count, sizeof(int));
                    write(ctop_fd[0][1], "ACK_READ", 9);
       
                    if (pending_count > 0) {
                        Booking* pending = malloc(pending_count * sizeof(Booking));
                        read(ptoc_fd[0][0], pending, pending_count * sizeof(Booking));
                        write(ctop_fd[0][1], "ACK_SENT", 9);
       
                        // Process bookings
                        int acceptList[MAX_BOOKINGS] = {0};
                        int acceptCount = 0;
                       
                        if (strcmp(algorithm, "fcfs") == 0) {
                            memset(acceptList, 0, sizeof(acceptList));
                            FCFS_Scheduler(pending, pending_count, acceptList, &acceptCount);
                        } 
                        else if (strcmp(algorithm, "prio") == 0) {
                            memset(acceptList, 0, sizeof(acceptList));
                            Priority_Scheduler(pending, pending_count, acceptList, &acceptCount);
                        }   
       
                        // Send results to parent
                        char msg_p0[9];
                        read(ptoc_fd[0][0], msg_p0, 9);
                        if(strcmp(msg_p0, "ACK_OKAY") != 0) {
                            break;
                        }

                        write(ctop_fd[0][1], &acceptCount, sizeof(int));
                        read(ptoc_fd[0][0], msg_p0, 9);
                        if(strcmp(msg_p0, "ACK_RECV") != 0) {
                            break;
                        }

                        write(ctop_fd[0][1], acceptList, acceptCount * sizeof(int));
                        char ack_list[9];
                        read(ptoc_fd[0][0], ack_list, 9);
                        if (strcmp(ack_list, "ACK_LIST") != 0) {
                            break;
                        }
                       
                        free(pending);
                    }
                }
            }
            
           
            /* Output Module - Child Process*/
            else if (i == 1) {  // 2nd Child -> Ouput Module

                close(ptoc_fd[i][1]); // Close parent's write end
                close(ctop_fd[i][0]); // Close parent's read end
                // receive from parent
               
                char msg[6] = {0};
                if (read(ptoc_fd[i][0], msg, 5) > 0 && strcmp(msg, "START") == 0) {
                    write(ctop_fd[i][1], "READY", 5); // Send "READY" acknowledgment to parent
                }

                while (1) {
                    char algorithm[6] = {0};

                    int algo_read = read(ptoc_fd[1][0], algorithm, 6);
                    if (algo_read <= 0) break;

                    if (algo_read <= 0 || strcmp(algorithm, "EXIT") == 0) {
                        break; // Exit the loop and terminate the child process
                    }

                    write(ctop_fd[1][1], "ACK_ALGO", 9);

                    int schedCount = 0;
                    if (read(ptoc_fd[1][0], &schedCount, sizeof(int)) > 0) {

                        write(ctop_fd[1][1], "ACK_COUNTER", 12);
                    }
               
                    Booking* schedList = malloc(schedCount * sizeof(Booking));
                    if (!schedList) {
                        fprintf(stderr, "Error: Failed to allocate memory for Booking List.\n");
                        break;
                    }
               
                    if (read(ptoc_fd[1][0], schedList, schedCount * sizeof(Booking)) > 0) {
                        write(ctop_fd[1][1], "ACK_LIST", 9);
                    }

                    int acceptCount = 0;
                    if (read(ptoc_fd[1][0], &acceptCount, sizeof(int)) > 0) {
                        write(ctop_fd[1][1], "ACK_COUNTER", 12);
                    }

                    int* acceptIdx = malloc(acceptCount * sizeof(int));
                    if (read(ptoc_fd[1][0], acceptIdx, acceptCount * sizeof(Booking)) > 0) {
                        print_bookings(schedList, schedCount, acceptIdx, acceptCount, algorithm);
                        write(ctop_fd[1][1], "ACK_INDX", 9);
                    }
               
                    free(schedList);
                    free(acceptIdx);
                }
            }


            /* Analyzer Module - 3rd Child */
            else if (i == 2) {
                close(ptoc_fd[i][1]); // Close parent's write end
                close(ctop_fd[i][0]); // Close parent's read end

                while (1) {

                    char algorithm[6] = {0};

                    // Receive algorithm name
                    int bytes_read = read(ptoc_fd[i][0], algorithm, sizeof(algorithm));
                    if (bytes_read <= 0 || strcmp(algorithm, "EXIT") == 0) {
                        break; // Exit the loop and terminate the child process
                    }

                    write(ctop_fd[i][1], "ACK_ALGO", 9); // Send acknowledgment

                    int pending_count = 0;

                    // Receive pending count
                    if (read(ptoc_fd[i][0], &pending_count, sizeof(int)) <= 0) {
                        break; // Exit if no data is received
                    }
                    write(ctop_fd[i][1], "ACK_COUNTER", 12); // Send acknowledgment
            
                    // Allocate memory for pending bookings
                    Booking* pending_bookings = malloc(pending_count * sizeof(Booking));
                    if (!pending_bookings) {
                        fprintf(stderr, "Analyzer: Memory allocation failed for pending bookings.\n");
                        free(pending_bookings);
                        break;
                    }
            
                    // Receive pending bookings
                    if (read(ptoc_fd[i][0], pending_bookings, pending_count * sizeof(Booking)) <= 0) {
                        free(pending_bookings);
                        break; // Exit if no data is received
                    }
                    write(ctop_fd[i][1], "ACK_LIST", 9); // Send acknowledgment
            
                    int accept_count = 0;
            
                    // Receive accepted count
                    if (read(ptoc_fd[i][0], &accept_count, sizeof(int)) <= 0) {
                        free(pending_bookings);
                        break; // Exit if no data is received
                    }
                    write(ctop_fd[i][1], "ACK_COUNTER", 12); // Send acknowledgment
            
                    // Allocate memory for accepted indices
                    int* accepted_indices = malloc(accept_count * sizeof(int));
                    if (!accepted_indices) {
                        fprintf(stderr, "Analyzer: Memory allocation failed for accepted indices.\n");
                        free(pending_bookings);
                        free(accepted_indices);
                        exit(1);
                    }
            
                    // Receive accepted indices
                    if (read(ptoc_fd[i][0], accepted_indices, accept_count * sizeof(int)) <= 0) {
                        free(pending_bookings);
                        free(accepted_indices);
                        break; // Exit if no data is received
                    }
                    write(ctop_fd[i][1], "ACK_INDX", 9); // Send acknowledgment

                    // Receive invalid_command_count
                    int received_invalid_count = 0;
                    if (read(ptoc_fd[i][0], &received_invalid_count, sizeof(int)) <= 0) {
                        free(pending_bookings);
                        free(accepted_indices);
                        break; // Exit if no data is received
                    }
                    write(ctop_fd[i][1], "ACK_INVALID", 12); // Send acknowledgment

                    // Analyzer Module: Process bookings and generate the report
                    FILE* fp = fopen("SPMS_Report_G34.txt", "a");
                    if (!fp) {
                        perror("Analyzer: Failed to open report file");
                    } else {
                        fprintf(fp, "\n*** Parking Booking Manager – Summary Report ***\n");

                        // Find the earliest and latest booking dates
                        char earliest_date[11] = "9999-12-31";
                        char latest_date[11] = "0000-01-01";
                        for (int i = 0; i < pending_count; i++) {
                            if (strcmp(pending_bookings[i].date, earliest_date) < 0) {
                                strcpy(earliest_date, pending_bookings[i].date);
                            }
                            if (strcmp(pending_bookings[i].date, latest_date) > 0) {
                                strcpy(latest_date, pending_bookings[i].date);
                            }
                        }

                        int test_days = calculate_days_between(earliest_date, latest_date);
                        fprintf(fp, "Test Period: %s to %s (%d days)\n", earliest_date, latest_date, test_days);

                        // Performance for two algorithms
                        fprintf(fp, "\nPerformance:\nFor %s:\n", algorithm);
                        fprintf(fp, "Total Number of Bookings Received: %d\n", pending_count);
                        fprintf(fp, "Number of Bookings Assigned: %d\n", accept_count);
                        fprintf(fp, "Number of Bookings Rejected: %d\n", pending_count - accept_count);

                        // Calculate Time Slot Utilization
                        int total_slots = test_days * 24 * 3; // Total slots = days * 24 hours * 3
                        float total_occupied_hours = 0;
                        for (int i = 0; i < accept_count; i++) {
                            int idx = accepted_indices[i];
                            total_occupied_hours += pending_bookings[idx].duration; // Sum durations of accept bookings
                        }
                        float time_slot_utilization = (total_occupied_hours / total_slots) * 100;
                        fprintf(fp, "Utilization of Time Slot: %.1f%%\n", time_slot_utilization);

                        // Calculate Resource Utilization
                        int locker_used = 0, battery_used = 0, cable_used = 0, umbrella_used = 0, valet_used = 0, inflation_used = 0;
                        for (int i = 0; i < accept_count; i++) {
                            int idx = accepted_indices[i];
                            int current_duration = pending_bookings[idx].duration;
                            
                            char processed_essentials[MAX_ESSENTIALS][MAX_STRING_LENGTH] = {0};
                            int processed_count = 0;
                            
                            for (int j = 0; j < pending_bookings[idx].essential_count; j++) {
                                char current_essential[MAX_STRING_LENGTH];
                                strncpy(current_essential, pending_bookings[idx].essentials[j], MAX_STRING_LENGTH - 1);
                                current_essential[MAX_STRING_LENGTH - 1] = '\0';
                                to_lower_case(current_essential);
                                
                                // check whether has processed before
                                bool processed = false;
                                const char* pair = get_pair_essential(current_essential);
                                
                                for (int p = 0; p < processed_count; p++) {
                                    if (strcmp(current_essential, processed_essentials[p]) == 0 || 
                                        (pair && strcmp(pair, processed_essentials[p]) == 0)) {
                                        processed = true;
                                        break;
                                    }
                                }

                                if (!processed) {
                                    // for current device
                                    if (strcmp(current_essential, "locker") == 0) locker_used += current_duration;
                                    else if (strcmp(current_essential, "battery") == 0) battery_used += current_duration;
                                    else if (strcmp(current_essential, "cable") == 0) cable_used += current_duration;
                                    else if (strcmp(current_essential, "umbrella") == 0) umbrella_used += current_duration;
                                    else if (strcmp(current_essential, "valetpark") == 0) valet_used += current_duration;
                                    else if (strcmp(current_essential, "inflationservice") == 0) inflation_used += current_duration;

                                    // staticstic for paired
                                    if (pair) {
                                        if (strcmp(pair, "locker") == 0) locker_used += current_duration;
                                        else if (strcmp(pair, "battery") == 0) battery_used += current_duration;
                                        else if (strcmp(pair, "cable") == 0) cable_used += current_duration;
                                        else if (strcmp(pair, "umbrella") == 0) umbrella_used += current_duration;
                                        else if (strcmp(pair, "valetpark") == 0) valet_used += current_duration;
                                        else if (strcmp(pair, "inflationservice") == 0) inflation_used += current_duration;
                                    }

                                    // mark as processed
                                    strncpy(processed_essentials[processed_count], current_essential, MAX_STRING_LENGTH - 1);
                                    processed_count++;
                                    if (pair) {
                                        strncpy(processed_essentials[processed_count], pair, MAX_STRING_LENGTH - 1);
                                        processed_count++;
                                    }
                                }
                            }
                        }

                        fprintf(fp, "\nResource Utilization:\n");
                        fprintf(fp, "Locker - %.1f%%\n", (locker_used / (float)(test_days * 24 * MAX_RESOURCES)) * 100);
                        fprintf(fp, "Battery - %.1f%%\n", (battery_used / (float)(test_days * 24 * MAX_RESOURCES)) * 100);
                        fprintf(fp, "Cable - %.1f%%\n", (cable_used / (float)(test_days * 24 * MAX_RESOURCES)) * 100);
                        fprintf(fp, "Umbrella - %.1f%%\n", (umbrella_used / (float)(test_days * 24 * MAX_RESOURCES)) * 100);
                        fprintf(fp, "Valet - %.1f%%\n", (valet_used / (float)(test_days * 24 * MAX_RESOURCES)) * 100);
                        fprintf(fp, "Inflation - %.1f%%\n", (inflation_used / (float)(test_days * 24 * MAX_RESOURCES)) * 100);

                        // Invalid Requests
                        fprintf(fp, "\nInvalid request(s) made: %d\n", received_invalid_count);

                        fclose(fp);
                    }
                }
            }
            //close used pipe ends
            close(ptoc_fd[i][0]);
            close(ctop_fd[i][1]);
            exit(0);
        }
    }
       

    // Parent process
    // Close unused pipe ends
    for (int j = 0; j < 3; j++) {
        close(ptoc_fd[j][0]);
        close(ctop_fd[j][1]);
    }

    // Parent signal child proceses to start -> parallel processing
    for(int j = 0; j < 2; j++){
        write(ptoc_fd[j][1], "START", 5);
    }

    // Wait for "READY" from child
    for(int k = 0; k < 2; k++){
        char ready_msg[6] = {0};
        if (read(ctop_fd[k][0], ready_msg, sizeof(ready_msg) - 1) > 0 && strcmp(ready_msg, "READY") == 0) {
            // printf("Parent received READY signal from Child %d.\n", k);
        }
    }

    char input[256] = {0};
    while(1) {
        printf("\nPlease enter booking:\n");
        if (fgets(input, sizeof(input), stdin) == NULL) {
            break;
        }
        input[strcspn(input, "\n")] = 0;
        char test[256];
        strcpy(test, input);

        // NEED EDIT
        if (strcmp(input, "endProgram;") == 0) {
            printf("-> Bye!\n");
        
            // Send termination signal to all child processes
            for (int i = 0; i < 3; i++) {
                write(ptoc_fd[i][1], "EXIT", 5);
            }
        
            // Wait for all child processes to terminate
            for (int i = 0; i < 3; i++) {
                int status;
                waitpid(-1, &status, 0);
            }
        
            free(allBookings.bookings);
            free(fcfs_results.accepted_idx);
            free(fcfs_results.rejected_idx);
            free(prio_results.accepted_idx);
            free(prio_results.rejected_idx);
            break;
        }
       
        char *token = strtok(input, " ");
        if (token == NULL) continue;

        if(strcmp(token, "addParking") == 0 ||
            strcmp(token, "addReservation") == 0 ||
            strcmp(token, "bookEssentials") == 0 ||
            strcmp(token, "addEvent") == 0) {
            command_processor(test);
        }

        else if (strcmp(token, "printBookings") == 0) {
            char algorithm[6] = {0};
            token = strtok(NULL, " ");

            if (token) {
                strncpy(algorithm, token + 1, sizeof(algorithm) - 1); // Skip the leading dash
                algorithm[sizeof(algorithm) - 1] = '\0'; // Ensure null-termination
        
                // Find the last semicolon in the string and remove it
                char* last_semicolon = strrchr(algorithm, ';');
                if (*last_semicolon != ';') {
                    printf("Error: Command must end with a semicolon\n");
                    invalid_command_count++;
                    continue;
                }
                if (last_semicolon) {
                    *last_semicolon = '\0'; // Replace the semicolon with a null terminator
                }
            }

            const char* algorithms[] = {"fcfs", "prio"};
            SchedulerResults* results[] = {&fcfs_results, &prio_results};
            int numAlgorithms = 2;
            int start = 0;

            if (strcmp(algorithm, "fcfs") == 0) numAlgorithms = 1;
            else if (strcmp(algorithm, "prio") == 0) start = 1;

            Booking* pending_bookings;
            int pending_count = 0;
            int acceptCounter = 0;
            SchedulerResults* res;

            for (int a = start; a < numAlgorithms; a++) {
                // Send algorithm string to Scheduler (child 0)
                write(ptoc_fd[0][1], algorithms[a], 6);
                char ack_algo[9] = {0};
                read(ctop_fd[0][0], ack_algo, 9);
                if (strcmp(ack_algo, "ACK_ALGO") != 0) {
                    fprintf(stderr, "Parent: Missing ACK_ALGO\n");
                    break;
                }

                // Get pending bookings (assume allBookings.booking_count is total pending)
                pending_count = allBookings.booking_count;
                pending_bookings = malloc(pending_count * sizeof(Booking));
                if (pending_count == 0) {
                    printf("Error: No pending bookings available for processing.\n");
                    invalid_command_count++; // Increment invalid command count
                    break;
                }
                if (!pending_bookings) {
                    fprintf(stderr, "Error: Memory allocation for pending bookings failed.\n");
                    break;
                }

                for (int i = 0; i < allBookings.booking_count; i++) {
                    if (allBookings.bookings[i].status == STATUS_PENDING) {
                        memcpy(&pending_bookings[i], &allBookings.bookings[i], sizeof(Booking));
                    }
                }

                // Send pending count and bookings to Scheduler
                write(ptoc_fd[0][1], &pending_count, sizeof(int));
                char ack_read[9] = {0};
                read(ctop_fd[0][0], ack_read, 9);
                if (strcmp(ack_read, "ACK_READ") != 0) {
                    break;
                }
                write(ptoc_fd[0][1], pending_bookings, pending_count * sizeof(Booking));
                char ack_sent[9] = {0};
                read(ctop_fd[0][0], ack_sent, 9);
                if (strcmp(ack_sent, "ACK_SENT") != 0) {
                    break;
                }

                // Tell scheduler that we're ready to receive results
                write(ptoc_fd[0][1], "ACK_OKAY", 9);
                res = results[a];
                res->total_received = pending_count;
                read(ctop_fd[0][0], &acceptCounter, sizeof(int));
                write(ptoc_fd[0][1], "ACK_RECV", 9);
                res->accepted_idx = malloc(acceptCounter * sizeof(int));
                if (!res->accepted_idx) {
                    fprintf(stderr, "Error: Memory allocation for acceptList failed.\n");
                    break;
                }
                read(ctop_fd[0][0], res->accepted_idx, acceptCounter * sizeof(int));
                write(ptoc_fd[0][1], "ACK_LIST", 9);
                res->accepted_count = acceptCounter;

                // Update rejected bookings in SchedulerResults
                res->rejected_count = 0;
                res->rejected_idx = malloc(pending_count * sizeof(int)); // worst-case
                if (!res->rejected_idx) {
                    fprintf(stderr, "Error: Memory allocation for rejectList failed.\n");
                    free(pending_bookings);
                    free(res->accepted_idx);
                    exit(1);
                }
                
                int m = 0; // Pointer to the next accepted index
                for (int i = 0; i < pending_count; i++) {
                    if (m < acceptCounter && i == res->accepted_idx[m]) {
                        m++; // Skip accepted bookings
                    } else {
                        res->rejected_idx[res->rejected_count++] = i;
                    }
                }

                // Forward results to Output Module
                write(ptoc_fd[1][1], algorithms[a], 6);

                char ack_algo_c1[9];
                read(ctop_fd[1][0], ack_algo_c1, 9); // Wait for ACK_ALGO from Child 1
                if (strcmp(ack_algo_c1, "ACK_ALGO") != 0) {
                    break;;
                }

                write(ptoc_fd[1][1], &pending_count, sizeof(int)); // Send pending count

                char ack[12];
                read(ctop_fd[1][0], ack, sizeof(ack));
                if (strcmp(ack, "ACK_COUNTER") != 0) {
                    break;
                }

                write(ptoc_fd[1][1], pending_bookings, pending_count * sizeof(Booking)); // Send pending bookings

                char final_ack[9];
                read(ctop_fd[1][0], final_ack, sizeof(final_ack));
                if (strcmp(final_ack, "ACK_LIST") != 0) {
                    break;
                }

                write(ptoc_fd[1][1], &acceptCounter, sizeof(int)); // Send accepted count

                char ack_1[12];
                read(ctop_fd[1][0], ack_1, sizeof(ack));
                if (strcmp(ack_1, "ACK_COUNTER") != 0) {
                    break;
                }

                write(ptoc_fd[1][1], res->accepted_idx, acceptCounter * sizeof(int)); // Send accepted list
                
                char finall_ack[9];
                read(ctop_fd[1][0], finall_ack, sizeof(finall_ack));
                if (strcmp(finall_ack, "ACK_INDX") != 0) {
                    break;
                }
            }

            if(strcmp(algorithm, "ALL") == 0){
                for (int a = 0; a < numAlgorithms; a++){
                    SchedulerResults* res = results[a];

                    // Send algorithm name to Analyzer Module
                    write(ptoc_fd[2][1], algorithms[a], 6); // Send algorithm name
                    char ack_algo[9] = {0};
                    read(ctop_fd[2][0], ack_algo, sizeof(ack_algo)); // Wait for acknowledgment
                    if (strcmp(ack_algo, "ACK_ALGO") != 0) {
                        fprintf(stderr, "Parent: Missing ACK_ALGO from Analyzer Module.\n");
                        break;
                    }

                    // Communicate with Analyzer Module (child process 2)
                    write(ptoc_fd[2][1], &pending_count, sizeof(int)); // Send pending count to Analyzer
                    char ack[12] = {0};
                    read(ctop_fd[2][0], ack, sizeof(ack)); // Wait for acknowledgment
                    if (strcmp(ack, "ACK_COUNTER") != 0) {
                        fprintf(stderr, "Parent: Missing ACK_COUNTER from Analyzer Module.\n");
                        break;
                    }

                    // Send pending bookings
                    write(ptoc_fd[2][1], pending_bookings, pending_count * sizeof(Booking)); // Send pending bookings
                    char final_ack[9] = {0};
                    read(ctop_fd[2][0], final_ack, sizeof(final_ack)); // Wait for acknowledgment
                    if (strcmp(final_ack, "ACK_LIST") != 0) {
                        fprintf(stderr, "Parent: Missing ACK_LIST from Analyzer Module.\n");
                        break;
                    }

                    // Send accepted count
                    write(ptoc_fd[2][1], &acceptCounter, sizeof(int)); // Send accepted count
                    char ack_1[12] = {0};
                    read(ctop_fd[2][0], ack_1, sizeof(ack_1)); // Wait for acknowledgment
                    if (strcmp(ack_1, "ACK_COUNTER") != 0) {
                        fprintf(stderr, "Parent: Missing ACK_COUNTER from Analyzer Module.\n");
                        break;
                    }

                    // Send accepted indices
                    write(ptoc_fd[2][1], res->accepted_idx, acceptCounter * sizeof(int)); // Send accepted indices
                    char finall_ack[9] = {0};
                    read(ctop_fd[2][0], finall_ack, sizeof(finall_ack)); // Wait for acknowledgment
                    if (strcmp(finall_ack, "ACK_INDX") != 0) {
                        fprintf(stderr, "Parent: Missing ACK_INDX from Analyzer Module.\n");
                        break;
                    }

                    // Send invalid command counter
                    write(ptoc_fd[2][1], &invalid_command_count, sizeof(int)); // Send invalid command count
                    char ack_invalid[12] = {0};
                    read(ctop_fd[2][0], ack_invalid, sizeof(ack_invalid)); // Wait for acknowledgment
                    if (strcmp(ack_invalid, "ACK_INVALID") != 0) {
                        fprintf(stderr, "Parent: Missing ACK_INVALID from Analyzer Module.\n");
                        break;
                    }          
                }
            }
            
            free(pending_bookings);
            printf("-> [Done]");
        }

        else if (strcmp(token, "addBatch") == 0) {
            char filename[MAX_STRING_LENGTH];
            token = strtok(NULL, " ");
            if (token) {
                if (token[0] == '-') {
                    token++;
                }
                strcpy(filename, token);
                filename[strcspn(filename, ";")] = '\0';
                process_batch_file(filename);
            }
        }

        else{
            printf("Unknown command: %s\n", token);
        }
       
    }
    return 0;
}

