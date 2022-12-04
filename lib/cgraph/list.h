#pragma once

#include <assert.h>
#include <cgraph/alloc.h>
#include <stdbool.h>
#include <stdlib.h>

/** create a new list type and its associated member functions
 *
 * \param name Type name to give the list container
 * \param type Type of the elements the list will store
 */
#define DEFINE_LIST(name, type)                                                \
                                                                               \
  /** list container                                                           \
   *                                                                           \
   * All members of this type are considered private. They should only be      \
   * accessed through the functions below.                                     \
   */                                                                          \
  typedef struct {                                                             \
    type *data;      /* backing storage */                                     \
    size_t size;     /* number of elements in the list */                      \
    size_t capacity; /* available storage slots */                             \
  } name##_t;                                                                  \
                                                                               \
  /** create a new list                                                        \
   *                                                                           \
   * This function is provided for convenience, but it the equivalent of zero  \
   * initialization, `list_t list = {0}`. In general, the latter should be     \
   * preferred as it can be understood locally.                                \
   *                                                                           \
   * \return A new empty list                                                  \
   */                                                                          \
  static inline name##_t name##_new(void) { return (name##_t){0}; }            \
                                                                               \
  /** get the number of elements in a list */                                  \
  static size_t name##_size(const name##_t *list) {                            \
    assert(list != NULL);                                                      \
    return list->size;                                                         \
  }                                                                            \
                                                                               \
  /** does this list contain no elements? */                                   \
  static inline bool name##_is_empty(const name##_t *list) {                   \
    assert(list != NULL);                                                      \
    return name##_size(list) == 0;                                             \
  }                                                                            \
                                                                               \
  static inline void name##_append(name##_t *list, type item) {                \
    assert(list != NULL);                                                      \
                                                                               \
    /* do we need to expand the backing storage? */                            \
    if (list->size == list->capacity) {                                        \
      size_t c = list->capacity == 0 ? 1 : (list->capacity * 2);               \
      list->data = gv_recalloc(list->data, list->capacity, c, sizeof(type));   \
      list->capacity = c;                                                      \
    }                                                                          \
                                                                               \
    list->data[list->size] = item;                                             \
    ++list->size;                                                              \
  }                                                                            \
                                                                               \
  /** retrieve an element from a list                                          \
   *                                                                           \
   * \param list List to operate on                                            \
   * \param index Element index to get                                         \
   * \return Element at the given index                                        \
   */                                                                          \
  static inline type name##_get(const name##_t *list, size_t index) {          \
    assert(list != NULL);                                                      \
    assert(index < list->size && "index out of bounds");                       \
    return list->data[index];                                                  \
  }                                                                            \
                                                                               \
  /** assign to an element in a list                                           \
   *                                                                           \
   * \param list List to operate on                                            \
   * \param index Element to assign to                                         \
   * \param item Value to assign                                               \
   */                                                                          \
  static inline void name##_set(name##_t *list, size_t index, type item) {     \
    assert(list != NULL);                                                      \
    assert(index < list->size && "index out of bounds");                       \
    list->data[index] = item;                                                  \
  }                                                                            \
                                                                               \
  /** access an element in a list for the purpose of modification              \
   *                                                                           \
   * Because this acquires an internal pointer into the list structure, `get`  \
   * and `set` should be preferred over this function. `get` and `set` are     \
   * easier to reason about. In particular, the pointer returned by this       \
   * function is invalidated by any list operation that may reallocate the     \
   * backing storage (e.g. `shrink_to_fit`).                                   \
   *                                                                           \
   * \param list List to operate on                                            \
   * \param index Element to get a pointer to                                  \
   * \return Pointer to the requested element                                  \
   */                                                                          \
  static inline type *name##_at(name##_t *list, size_t index) {                \
    assert(list != NULL);                                                      \
    assert(index < list->size && "index out of bounds");                       \
    return &list->data[index];                                                 \
  }                                                                            \
                                                                               \
  /** remove all elements from a list */                                       \
  static inline void name##_clear(name##_t *list) {                            \
    assert(list != NULL);                                                      \
    list->size = 0;                                                            \
  }                                                                            \
                                                                               \
  /** shrink or grow the list to the given size                                \
   *                                                                           \
   * \param list List to operate on                                            \
   * \param size New size of the list                                          \
   * \param value Default to assign to any new elements                        \
   */                                                                          \
  static inline void name##_resize(name##_t *list, size_t size, type value) {  \
    assert(list != NULL);                                                      \
                                                                               \
    while (list->size < size) {                                                \
      name##_append(list, value);                                              \
    }                                                                          \
    list->size = size;                                                         \
  }                                                                            \
                                                                               \
  /** deallocate unused backing storage, shrinking capacity to size */         \
  static inline void name##_shrink_to_fit(name##_t *list) {                    \
    assert(list != NULL);                                                      \
                                                                               \
    if (list->size > list->capacity) {                                         \
      list->data =                                                             \
          gv_recalloc(list->data, list->capacity, list->size, sizeof(type));   \
      list->capacity = list->size;                                             \
    }                                                                          \
  }                                                                            \
                                                                               \
  /** free resources associated with a list */                                 \
  static inline void name##_free(name##_t *list) {                             \
    assert(list != NULL);                                                      \
    free(list->data);                                                          \
    *list = (name##_t){0};                                                     \
  }                                                                            \
                                                                               \
  /** create a new list from a bare array and element count                    \
   *                                                                           \
   * This can be useful when receiving data from a caller who does not use     \
   * this API, but the callee wants to. Note that the backing data for the     \
   * array must have been heap-allocated.                                      \
   *                                                                           \
   * \param data Array of existing elements                                    \
   * \param size Number of elements pointed to by `data`                       \
   * \return A managed list containing the provided elements                   \
   */                                                                          \
  static inline name##_t name##_attach(type *data, size_t size) {              \
    assert(data != NULL || size == 0);                                         \
    return (name##_t){.data = data, .size = size, .capacity = size};           \
  }                                                                            \
                                                                               \
  /** transform a managed list into a bare array                               \
   *                                                                           \
   * This can be useful when needing to pass data to a callee who does not     \
   * use this API. The managed list is emptied and left in a state where it    \
   * can be reused for other purposes.                                         \
   *                                                                           \
   * \param list List to operate on                                            \
   * \return A pointer to an array of the `list->size` elements                \
   */                                                                          \
  static inline type *name##_detach(name##_t *list) {                          \
    assert(list != NULL);                                                      \
    type *data = list->data;                                                   \
    *list = (name##_t){0};                                                     \
    return data;                                                               \
  }