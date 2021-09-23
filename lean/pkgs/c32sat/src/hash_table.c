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
#include <stdlib.h>
#include <assert.h>
#include "hash_table.h"
#include "bool.h"
#include "memory_management.h"
#include "c32sat_math.h"

static HashTableEntry *
create_hash_table_entry (void *key, void *data)
{
  HashTableEntry *entry = NULL;
  entry = (HashTableEntry *) malloc_c32sat (sizeof (HashTableEntry));
  entry->key = key;
  entry->data = data;
  entry->next = NULL;
  return entry;
}

static void
delete_hash_table_entry (HashTableEntry * entry)
{
  assert (entry != NULL);
  free_c32sat (entry, sizeof (HashTableEntry));
}

HashTable *
create_hash_table (int power, unsigned int (*ptr_hash) (void *key),
                   Bool (*ptr_equals) (void *key1, void *key2),
                   void (*ptr_delete) (void *data))
{
  HashTable *table = NULL;
  int i = 0;
  assert (power >= 0 && ptr_hash != NULL && ptr_equals != NULL);
  table = (HashTable *) malloc_c32sat (sizeof (HashTable));
  table->size = 1 << min_c32sat_math (power, HASH_TABLE_MAX_POWER);
  table->num_elements = 0;
  table->ptr_hash = ptr_hash;
  table->ptr_equals = ptr_equals;
  table->ptr_delete = ptr_delete;
  table->chains =
    (HashTableEntry **) malloc_c32sat (sizeof (HashTableEntry *) *
                                       table->size);
  for (i = 0; i < table->size; i++)
    {
      table->chains[i] = NULL;
    }
  return table;
}

void
delete_hash_table (HashTable * table, Bool delete_data)
{
  int i = 0;
  HashTableEntry *entry = NULL;
  HashTableEntry *temp = NULL;
  assert (table != NULL);
  if (table->num_elements > 0)
    {
      for (i = 0; i < table->size; i++)
        {
          entry = table->chains[i];
          while (entry != NULL)
            {
              temp = entry->next;
              if (delete_data && table->ptr_delete != NULL)
                {
                  table->ptr_delete (entry->data);
                }
              delete_hash_table_entry (entry);
              entry = temp;
            }
        }
    }
  free_c32sat (table->chains, sizeof (HashTableEntry *) * table->size);
  free_c32sat (table, sizeof (HashTable));
}

static void
enlarge_hash_table (HashTable ** table)
{
  int i = 0;
  unsigned int hash = 0;
  HashTable *new_table =
    create_hash_table (log2_c32sat_math ((*table)->size) + 1,
                       (*table)->ptr_hash,
                       (*table)->ptr_equals,
                       (*table)->ptr_delete);
  HashTableEntry *cur = NULL;
  HashTableEntry *temp = NULL;
  for (i = 0; i < (*table)->size; i++)
    {
      cur = (*table)->chains[i];
      while (cur != NULL)
        {
          temp = cur->next;
          hash = (*table)->ptr_hash (cur->key) & (new_table->size - 1);
          cur->next = new_table->chains[hash];
          new_table->chains[hash] = cur;
          cur = temp;
        }
    }
  new_table->num_elements = (*table)->num_elements;
  (*table)->num_elements = 0;
  delete_hash_table (*table, b_false);
  *table = new_table;
}

void
insert_data_hash_table (HashTable ** table, void *key, void *data)
{
  unsigned int hash = 0;
  HashTableEntry *entry = NULL;
  assert (table != NULL && *table != NULL && key != NULL);
  if ((*table)->size < HASH_TABLE_MAX_SIZE
      && (*table)->size == (*table)->num_elements)
    {
      enlarge_hash_table (table);
    }
  hash = (*table)->ptr_hash (key) & ((*table)->size - 1);
  entry = create_hash_table_entry (key, data);
  entry->next = (*table)->chains[hash];
  (*table)->chains[hash] = entry;
  (*table)->num_elements++;
}

void *
lookup_hash_table (HashTable ** table, void *key)
{
  HashTableEntry *cur = NULL;
  Bool found = b_false;
  assert (table != NULL && *table != NULL && key != NULL);
  cur = (*table)->chains[(*table)->ptr_hash (key) & ((*table)->size - 1)];
  while (cur != NULL && !found)
    {
      if ((*table)->ptr_equals (cur->key, key))
        {
          found = b_true;
        }
      else
        {
          cur = cur->next;
        }
    }
  if (cur == NULL)
    {
      return NULL;
    }
  return cur->data;
}

void *
remove_data_hash_table (HashTable ** table, void *key)
{
  HashTableEntry *cur = NULL;
  HashTableEntry *prev = NULL;
  void *result = NULL;
  Bool found = b_false;
  assert (table != NULL && *table != NULL && key != NULL);
  cur = (*table)->chains[(*table)->ptr_hash (key) & ((*table)->size - 1)];
  while (!found && cur != NULL)
    {
      if ((*table)->ptr_equals (cur->key, key))
        {
          if (prev == NULL)
            {
              (*table)->chains[(*table)->
                               ptr_hash (key) & ((*table)->size - 1)] =
                cur->next;
            }
          else
            {
              prev->next = cur->next;
            }
          found = b_true;
        }
      else
        {
          prev = cur;
          cur = cur->next;
        }
    }
  if (cur != NULL)
    {
      result = cur->data;
      delete_hash_table_entry (cur);
      (*table)->num_elements--;
    }
  return result;
}
