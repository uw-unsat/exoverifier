/*
 Institute for Formal Models and Verification (FMV),
 Johannes Kepler University Linz, Austria
 
 Copyright (c) 2006, Robert Daniel Brummayer
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Neither the name of the FMV nor the names of its contributors may be
      used to endorse or promote products derived from this software without
      specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#ifndef _HASH_TABLE_H_
#define _HASH_TABLE_H_

#include "bool.h"

/** @brief Represents an entry in the hash table. */
struct HashTableEntry
{
  /** The key of the the entry */
  void *key;
  /** The data of the entry */
  void *data;
  /** The next element in the hash chain */
  struct HashTableEntry *next;
};

typedef struct HashTableEntry HashTableEntry;

/** @brief Represents a hash table. */ struct HashTable
{
  /** The size represents the number of hash chains */
  int size;
  /** The number of elements in the hash table */
  int num_elements;
  /** The function which computes the hash value of a key */
  unsigned int (*ptr_hash) (void *key);
  /** The function which determines if two keys are equal */
    Bool (*ptr_equals) (void *key1, void *key2);
  /** The function which is used for deleting elements */
  void (*ptr_delete) (void *data);
  /** The hash table chains */
  HashTableEntry **chains;
};

typedef struct HashTable HashTable;

/** Maximum power of the hash table */
#define HASH_TABLE_MAX_POWER 24
/** Maximum size of the hash table */
#define HASH_TABLE_MAX_SIZE (1 << HASH_TABLE_MAX_POWER)

/** Creates a hash table.
 * @param power The power of the table. A power of 4 means 
 * for example that the size of the table is (1 << 4) = 16.
 * The minimum of power and @ref HASH_TABLE_MAX_POWER 
 * will be used.
 * @param ptr_hash The function which computes the hash value
 * of a key
 * @param ptr_equals The function which compares two entries
 * of the hash table by comparing their keys.
 * @param ptr_delete The function which can be used for 
 * destroying data entries. If @ref delete_hash_table is 
 * called with delete_data = @ref b_true this function is
 * called on every data in this table. If this is function 
 * is not needed NULL can be passed.
 */
HashTable *create_hash_table (int power,
                              unsigned int (*ptr_hash) (void *data),
                              Bool (*ptr_equals) (void *data1, void *data2),
                              void (*ptr_delete) (void *data));

/** Deletes a hash table from memory. If the number of elements
 * of the table is 0 then the collision chains won't be 
 * traversed for deleting hash table entries.
 * @param table The table which has to be deleted 
 * @param delete_data If this parameter is @ref b_true then 
 * the function for deleting data of the table will be called
 * on every data element in the table
 */
void delete_hash_table (HashTable * table, Bool delete_data);

/** Inserts data which is associated with a key into a hash table.
 * The hash table grows automatically.
 * @param table The corresponding hash table
 * @param key The corresponding key 
 * @param data The data which has to be inserted
 */
void insert_data_hash_table (HashTable ** table, void *key, void *data);

/** Returns the data of which is associated with the key.
 * @param table The corresponding hash table
 * @param key The key != NULL which is associated with the data
 * @return The data associated with the key or null if the key couldn't be found
 */
void *lookup_hash_table (HashTable ** table, void *key);

/** Removes an element and its key from a hash table and returns
 * the element. The hash table does not shrink automatically.
 * @param table The corresponding hash table
 * @param key The key != NULL which is associated with the data
 * which has to be removed
 * @return The data which has been removed from the hash table
 * or NULL if the hash table didn't contain the data associated
 * with the key
 */
void *remove_data_hash_table (HashTable ** table, void *key);

#endif
