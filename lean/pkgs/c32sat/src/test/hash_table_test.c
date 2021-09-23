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
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "hash_table_test.h"
#include "test_logging.h"
#include "../hash_table.h"
#include "../bool.h"
#include "../memory_management.h"
#include "../error_management.h"

Bool
hash_table_test_equals_string (void *key1, void *key2)
{
  if (strcmp ((char *) key1, (char *) key2) == 0)
    {
      return b_true;
    }
  return b_false;
}

unsigned int
hash_table_test_hash_string (void *key)
{
  unsigned int result = 0;
  char *cur = (char *) key;
  while (*cur)
    {
      result += *cur;
      cur++;
    }
  return result;
}

void
hash_table_test_delete_char_buffer (void *data)
{
  free_c32sat (data, sizeof (char) * (strlen ((char *) data) + 1));
}

void
test_create_delete_hash_table ()
{
  char *buffer = NULL;
  HashTable *table = NULL;
  HashTableEntry *entry1 = NULL;
  HashTableEntry *entry2 = NULL;
  HashTableEntry *entry3 = NULL;
  const int key1 = 3;
  const int key2 = 4;
  const int key3 = 5;
  const int power = 10;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  table =
    create_hash_table (power, hash_table_test_hash_string,
                       hash_table_test_equals_string, NULL);
  assert (table->size == 1 << power);
  assert (table->num_elements == 0);
  assert (table->ptr_hash == hash_table_test_hash_string);
  assert (table->ptr_equals == hash_table_test_equals_string);
  assert (table->chains != NULL);
  for (i = 0; i < table->size; i++)
    {
      assert (table->chains[i] == NULL);
    }
  entry1 = (HashTableEntry *) malloc_c32sat (sizeof (HashTableEntry));
  entry1->key = (void *) &key1;
  entry1->data = (void *) &entry1;
  entry2 = (HashTableEntry *) malloc_c32sat (sizeof (HashTableEntry));
  entry2->key = (void *) &key2;
  entry2->data = (void *) &entry2;
  entry3 = (HashTableEntry *) malloc_c32sat (sizeof (HashTableEntry));
  entry3->key = (void *) &key3;
  entry3->data = (void *) &entry3;
  entry1->next = entry2;
  entry2->next = entry3;
  entry3->next = NULL;
  table->chains[1] = entry1;
  table->num_elements = 3;
  delete_hash_table (table, b_false);
  table =
    create_hash_table (power, hash_table_test_hash_string,
                       hash_table_test_equals_string,
                       hash_table_test_delete_char_buffer);
  buffer = (char *) malloc_c32sat (sizeof (char) * 3);
  strcpy (buffer, "ab");
  entry1 = (HashTableEntry *) malloc_c32sat (sizeof (HashTableEntry));
  entry1->key = (void *) &key1;
  entry1->data = (void *) buffer;
  entry1->next = NULL;
  table->chains[1] = entry1;
  table->num_elements = 1;
  delete_hash_table (table, b_true);
  finalise_memory_management ();
}

void
test_hash_table_insert_data ()
{
  HashTable *table = NULL;
  HashTableEntry *temp = NULL;
  HashTableEntry *temp2 = NULL;
  char *key1 = "A";
  char *key2 = "B";
  char *key3 = "AB";
  char *key4 = "BA";
  int data1 = 1;
  int data2 = 2;
  int data3 = 3;
  int data4 = 4;
  const int power = 10;
  init_error_management (stderr);
  init_memory_management ();
  table =
    create_hash_table (power, hash_table_test_hash_string,
                       hash_table_test_equals_string, NULL);
  assert (table->num_elements == 0);
  insert_data_hash_table (&table, (void *) key1, (void *) &data1);
  assert (table->num_elements == 1);
  insert_data_hash_table (&table, (void *) key2, (void *) &data2);
  assert (table->num_elements == 2);
  insert_data_hash_table (&table, (void *) key3, (void *) &data3);
  assert (table->num_elements == 3);
  temp = (HashTableEntry *) table->chains[65];
  assert (temp->key == (void *) key1);
  assert (temp->data == (void *) &data1);
  assert (temp->next == NULL);
  temp = (HashTableEntry *) table->chains[66];
  assert (temp->key == (void *) key2);
  assert (temp->data == (void *) &data2);
  assert (temp->next == NULL);
  temp = (HashTableEntry *) table->chains[131];
  assert (temp->key == (void *) key3);
  assert (temp->data == (void *) &data3);
  assert (temp->next == NULL);
  insert_data_hash_table (&table, (void *) key4, (void *) &data4);
  assert (table->num_elements == 4);
  temp2 = (HashTableEntry *) table->chains[131];
  assert (temp2->key == (void *) key4);
  assert (temp2->data == (void *) &data4);
  assert (temp2->next == temp);
  delete_hash_table (table, b_false);
  finalise_memory_management ();
}

void
test_hash_table_lookup ()
{
  HashTable *table = NULL;
  char *key1 = "A";
  char *key2 = "B";
  char *key3 = "AB";
  char *key4 = "BA";
  char *key5 = "XYZ";
  int data1 = 1;
  int data2 = 2;
  int data3 = 3;
  int data4 = 4;
  init_error_management (stderr);
  init_memory_management ();
  table =
    create_hash_table (8, hash_table_test_hash_string,
                       hash_table_test_equals_string, NULL);
  insert_data_hash_table (&table, (void *) key1, (void *) &data1);
  insert_data_hash_table (&table, (void *) key2, (void *) &data2);
  insert_data_hash_table (&table, (void *) key3, (void *) &data3);
  insert_data_hash_table (&table, (void *) key4, (void *) &data4);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  assert (lookup_hash_table (&table, (void *) key2) == (void *) &data2);
  assert (lookup_hash_table (&table, (void *) key3) == (void *) &data3);
  assert (lookup_hash_table (&table, (void *) key4) == (void *) &data4);
  assert (lookup_hash_table (&table, (void *) key5) == (void *) NULL);
  delete_hash_table (table, b_false);
  finalise_memory_management ();
}

void
test_hash_table_enlargement ()
{
  HashTable *table = NULL;
  HashTableEntry *entry = NULL;
  char key1[] = { 1, 0 };
  char key2[] = { 2, 0 };
  char key3[] = { 3, 0 };
  char key4[] = { 7, 0 };
  char key5[] = { 5, 0 };
  int data1 = 1;
  int data2 = 2;
  int data3 = 3;
  int data4 = 4;
  int data5 = 5;
  init_error_management (stderr);
  init_memory_management ();
  table =
    create_hash_table (0, hash_table_test_hash_string,
                       hash_table_test_equals_string, NULL);
  assert (table->size == 1);
  assert (table->num_elements == 0);
  insert_data_hash_table (&table, (void *) key1, (void *) &data1);
  assert (table->size == 1);
  assert (table->num_elements == 1);
  entry = table->chains[0];
  assert (entry->data == (void *) &data1);
  assert (entry->key == (void *) key1);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  insert_data_hash_table (&table, (void *) key2, (void *) &data2);
  assert (table->size == 2);
  assert (table->num_elements == 2);
  entry = table->chains[0];
  assert (entry->data == (void *) &data2);
  assert (entry->key == (void *) key2);
  entry = table->chains[1];
  assert (entry->data == (void *) &data1);
  assert (entry->key == (void *) key1);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  assert (lookup_hash_table (&table, (void *) key2) == (void *) &data2);
  insert_data_hash_table (&table, (void *) key3, (void *) &data3);
  assert (table->size == 4);
  assert (table->num_elements == 3);
  assert (table->chains[0] == NULL);
  entry = table->chains[1];
  assert (entry->data == (void *) &data1);
  assert (entry->key == (void *) key1);
  entry = table->chains[2];
  assert (entry->data == (void *) &data2);
  assert (entry->key == (void *) key2);
  entry = table->chains[3];
  assert (entry->data == (void *) &data3);
  assert (entry->key == (void *) key3);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  assert (lookup_hash_table (&table, (void *) key2) == (void *) &data2);
  assert (lookup_hash_table (&table, (void *) key3) == (void *) &data3);
  insert_data_hash_table (&table, (void *) key4, (void *) &data4);
  assert (table->size == 4);
  assert (table->num_elements == 4);
  assert (table->chains[0] == NULL);
  entry = table->chains[1];
  assert (entry->data == (void *) &data1);
  assert (entry->key == (void *) key1);
  entry = table->chains[2];
  assert (entry->data == (void *) &data2);
  assert (entry->key == (void *) key2);
  entry = table->chains[3];
  assert (entry->data == (void *) &data4);
  assert (entry->key == (void *) key4);
  entry = table->chains[3]->next;
  assert (entry->data == (void *) &data3);
  assert (entry->key == (void *) key3);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  assert (lookup_hash_table (&table, (void *) key2) == (void *) &data2);
  assert (lookup_hash_table (&table, (void *) key3) == (void *) &data3);
  assert (lookup_hash_table (&table, (void *) key4) == (void *) &data4);
  insert_data_hash_table (&table, (void *) key5, (void *) &data5);
  assert (table->size == 8);
  assert (table->num_elements == 5);
  assert (table->chains[0] == NULL);
  entry = table->chains[1];
  assert (entry->data == (void *) &data1);
  assert (entry->key == (void *) key1);
  entry = table->chains[2];
  assert (entry->data == (void *) &data2);
  assert (entry->key == (void *) key2);
  entry = table->chains[3];
  assert (entry->data == (void *) &data3);
  assert (entry->key == (void *) key3);
  assert (table->chains[4] == NULL);
  entry = table->chains[5];
  assert (entry->data == (void *) &data5);
  assert (entry->key == (void *) key5);
  assert (table->chains[6] == NULL);
  entry = table->chains[7];
  assert (entry->data == (void *) &data4);
  assert (entry->key == (void *) key4);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  assert (lookup_hash_table (&table, (void *) key2) == (void *) &data2);
  assert (lookup_hash_table (&table, (void *) key3) == (void *) &data3);
  assert (lookup_hash_table (&table, (void *) key4) == (void *) &data4);
  assert (lookup_hash_table (&table, (void *) key5) == (void *) &data5);
  delete_hash_table (table, b_false);
  finalise_memory_management ();
}

void
test_hash_table_max_enlargement ()
{
  HashTable *table = NULL;
  char *key1 = "A";
  int data1 = 1;
  const int power = 10;
  init_error_management (stderr);
  init_memory_management ();
  table =
    create_hash_table (power, hash_table_test_hash_string,
                       hash_table_test_equals_string, NULL);
  table->size = HASH_TABLE_MAX_SIZE;
  insert_data_hash_table (&table, (void *) key1, (void *) &data1);
  assert (table->size == HASH_TABLE_MAX_SIZE);
  assert (lookup_hash_table (&table, (void *) key1) == (void *) &data1);
  table->size = 1 << power;
  delete_hash_table (table, b_false);
  finalise_memory_management ();
}

unsigned
hash_table_test_hash_const_zero (void *key)
{
  assert (key);
  return 0u;
}

Bool
hash_table_test_equals_ptr (void *key1, void *key2)
{
  return key1 == key2;
}

void
test_hash_table_remove_data ()
{
  HashTable *table = NULL;
  int data1 = 1;
  int data2 = 2;
  int data3 = 3;
  int key1 = 1;
  int key2 = 2;
  int key3 = 3;
  int key4 = 4;
  init_error_management (stderr);
  init_memory_management ();
  table =
    create_hash_table (2, hash_table_test_hash_const_zero,
                       hash_table_test_equals_ptr, NULL);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  insert_data_hash_table (&table, (void *) &key1, &data1);
  assert (table->chains[0] != NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (table->num_elements == 1);
  assert (remove_data_hash_table (&table, (void *) &key2) == NULL);
  assert (table->num_elements == 1);
  assert (remove_data_hash_table (&table, (void *) &key1) == &data1);
  assert (table->num_elements == 0);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  insert_data_hash_table (&table, (void *) &key1, &data1);
  insert_data_hash_table (&table, (void *) &key2, &data2);
  assert (remove_data_hash_table (&table, (void *) &key4) == NULL);
  assert (table->num_elements == 2);
  assert (remove_data_hash_table (&table, (void *) &key1) == &data1);
  assert (table->chains[0] != NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (remove_data_hash_table (&table, (void *) &key2) == &data2);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (table->num_elements == 0);
  insert_data_hash_table (&table, (void *) &key1, &data1);
  insert_data_hash_table (&table, (void *) &key2, &data2);
  insert_data_hash_table (&table, (void *) &key3, &data3);
  assert (remove_data_hash_table (&table, (void *) &key4) == NULL);
  assert (table->num_elements == 3);
  assert (table->chains[0] != NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (remove_data_hash_table (&table, (void *) &key2) == &data2);
  assert (remove_data_hash_table (&table, (void *) &key1) == &data1);
  assert (remove_data_hash_table (&table, (void *) &key3) == &data3);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (table->num_elements == 0);
  insert_data_hash_table (&table, (void *) &key1, &data1);
  insert_data_hash_table (&table, (void *) &key2, &data2);
  insert_data_hash_table (&table, (void *) &key3, &data3);
  assert (remove_data_hash_table (&table, (void *) &key4) == NULL);
  assert (table->num_elements == 3);
  assert (table->chains[0] != NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (remove_data_hash_table (&table, (void *) &key3) == &data3);
  assert (remove_data_hash_table (&table, (void *) &key2) == &data2);
  assert (remove_data_hash_table (&table, (void *) &key1) == &data1);
  assert (remove_data_hash_table (&table, (void *) &key4) == NULL);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == NULL);
  assert (table->chains[2] == NULL);
  assert (table->chains[3] == NULL);
  assert (table->num_elements == 0);
  assert (remove_data_hash_table (&table, (void *) &key3) == NULL);
  assert (remove_data_hash_table (&table, (void *) &key2) == NULL);
  assert (remove_data_hash_table (&table, (void *) &key1) == NULL);
  delete_hash_table (table, b_false);
  finalise_memory_management ();
}

void
run_hash_table_tests ()
{
  run_test (test_create_delete_hash_table);
  run_test (test_hash_table_insert_data);
  run_test (test_hash_table_lookup);
  run_test (test_hash_table_enlargement);
  run_test (test_hash_table_max_enlargement);
  run_test (test_hash_table_remove_data);
}
