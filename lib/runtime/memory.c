#include <stdlib.h>
#include <stdio.h>

// Should use a proper include for this but idk which it would be
// TODO FIXME
typedef long long int int64_t;

// Contains allocation functions for different kinds of regions

// Global region
// Number of bytes per block
#define GLOBAL_BLOCK_SIZE (1024 * 128)
int helium_global_remaining = 0;
void* helium_global_next;
void* helium_global_alloc(int size) {
  if (size > helium_global_remaining) {
    // Allocate new block
    helium_global_next = malloc(GLOBAL_BLOCK_SIZE);
    helium_global_remaining = GLOBAL_BLOCK_SIZE;
  }
  helium_global_remaining -= size;
  void* pointer = helium_global_next;
  helium_global_next += size;
  return pointer;
}

// Utilities to debug thunk evaluation
// To enable, uncomment calls to trace_thunk_eval and trace_thunk_done in IridiumLangEval.iridium
struct Thunk {
  long header;
  struct Thunk* next;
  char* fn;
  short remaining;
  short given;
  // ...arguments
};

void trace_thunk_idx(struct Thunk* thunk, int idx) {
  printf("Thunk, address = %ld, remaining = %d, given = %d, index in chain = %d\n", (long) thunk, thunk->remaining, thunk->given, idx);
  if (thunk->remaining == 32766) {
    printf("Evaluated\n\n");
    return;
  }

  printf("Function = ");
  char* charPtr = &thunk->fn[-1];
  while (*charPtr != 0) {
    putchar(*charPtr);
    charPtr = &charPtr[-1];
  }
  printf("\n");

  if (thunk->remaining == 32767) {
    printf("Blackhole\n\n");
    return;
  }

  if (thunk->remaining > 0) {
    printf("Unsaturated");
  } else if (thunk->remaining == 0) {
    printf("Saturated");
  } else if (thunk->given > -thunk->remaining) {
    printf("Oversaturated self");
  } else {
    printf("Oversaturated target");
  }

  if (thunk->next != thunk) {
    printf(", next: ");
    trace_thunk_idx(thunk->next, idx + 1);
  } else {
    printf("\n\n");
  }
}

void trace_thunk_eval(struct Thunk* thunk) {
  printf("Evaluating thunk: ");
  trace_thunk_idx(thunk, 0);
}

void trace_thunk_done(struct Thunk* thunk) {
  printf("Evaluated thunk %ld, value = %ld\n", (long) thunk, (long) thunk->fn);
}

struct Cursor {
  int64_t current_index;
  void* data;
};

struct ReadCursor {
  int64_t end_index;
  int64_t current_index;
  void* data;
};

void helium_memdump_cursor(struct Cursor* cursor) {
  printf("Cursor of size %lli with data:\n", cursor->current_index);

  for (int64_t i = 0; i < cursor->current_index; ++i) {
    printf("%i ", ((char*)cursor->data)[i]);
  }

  printf("\n");
}

struct Cursor* helium_new_cursor() {
  struct Cursor* ret_val = (struct Cursor*)malloc(sizeof(struct Cursor));
  ret_val->current_index = 0;
  ret_val->data = malloc(1024 * 256);

  printf("Made a thing!\n");
  return ret_val;
}

// Does NOT free the pointer to the cursor itself. Only prepares the cursor to
// be freed, i.e. removes its inner data!
// Assumes that the cursor has been initialized before!
// 
// This function should be called when the cursor gets GC'ed.
void helium_free_cursor(struct Cursor* cursor) {
  cursor->current_index = 0;
  free(cursor->data);
  cursor->data = NULL;

  printf("Freed a thing!\n");
}

struct Cursor* helium_write_cursor_at(struct Cursor* cursor, int64_t size, int64_t at, void* data) {
  for (int64_t i = 0; i < size; ++i) {
    int64_t write_index = at + i;
    // printf("Write index: %lli", write_index);
    char data_point = ((char*) data)[i];
    // printf(", Data point: %i\n", data_point);
    ((char*) cursor->data)[write_index] = data_point;
  }

  return cursor;
}

// Writes `size` bytes from `data` into `cursor`. Updates the current_index
// value of the cursor as well.
// Uuuh I'm not sure what causes this, but for some reason, the result of this
// function is assumed to be the new cursor to write into. We just return this
// cursor for now, but we might check to see if this behaviour should be
// changed instead.
struct Cursor* helium_write_cursor(struct Cursor* cursor, int64_t size, void* data) {
  helium_write_cursor_at(cursor, size, cursor->current_index, data);
  cursor->current_index += size;

  // printf("Wrote a thing of length: %lli!\n", size);
  // printf("First byte: %i\n", ((char*)data)[0]);
  // helium_memdump_cursor(cursor);

  printf("Wrote a thing!\n");
  return cursor;
}

// Writes the size of what has been written into the place where the size is
// supposed to be. The size needs to have space allocated before the object for
// which the size is stored; so, for instance, the following data structure:
// data Pair = Pair Int Int
// Will store the data like so:
// <ctor> <size of first Int> <first Int> <size of second Int> <second Int>
// This is the current way, but this function can work with any layout.

// The names of the parameters are a bit odd, but I can't think of any better
// ones. The first parameter is the index to write to, so where to _store_ the
// size. The second parameter is where the size needs to be calculated from, so
// where the field _starts_. The cursor knows where the field _ends_, so the
// second and third parameter together allow to calculate the size.
struct Cursor* helium_write_cursor_size(int size_index, int size_start, struct Cursor* cursor) {
  int size = cursor->current_index - size_start;
  printf("Writing size: %i\n", size);
  return helium_write_cursor_at(cursor, sizeof(size), size_index, (void*)&size);
}

// Are these cursors the same cursor?
// TODO make sure that these cursors exist lmaooo
struct ReadCursor* helium_finish_cursor(struct Cursor* cursor_start, struct Cursor* cursor_end) {
  helium_memdump_cursor(cursor_start);
  return NULL;
}

