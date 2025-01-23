/*
   Copyright (c) 2025, MariaDB

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1335  USA */

/**
  @file

    Contains estimate_post_group_cardinality() which estimates cardinality
    after GROUP BY operation is applied.
*/

#include "mariadb.h"
#include "sql_priv.h"
#include "sql_select.h"
#include "sql_statistics.h"
#include "opt_trace.h"

static
double estimate_table_group_cardinality(JOIN *join, Item ***group_list,
                                        Item* const *end);

inline bool has_one_bit_set(table_map val)
{
  return val && !(val & (val-1));
}

int cmp_items_by_used_tables(const void *a_val, const void *b_val)
{
  table_map v1= ((Item*)a_val)->used_tables();
  table_map v2= ((Item*)a_val)->used_tables();
  return v1 > v2 ? 1 : (v1 < v2 ? -1 : 0);
}


/*
  @brief
    Given a SELECT with GROUP BY clause, estimate the cardinality of output
    after the grouping operation is performed.

  @detail
    Consider a query

      SELECT ...
      FROM t1, t2, t3 ...
      WHERE ...
      GROUP BY
        col1, col2, ...

    Join optimizer produces an estimate of record cobinations after all tables
    are joined.
    GROUP BY operation combines groups of rows into one and leaves fewer rows
    as output.

    We use these approaches to estimate the number of groups:

    1. Number of rows in a table. In "GROUP BY t1.col, t1.col2", it doesn't
    matter how many rows other join tables have. We can say that there will
    be at most #rows(t1) groups.

    2. Number of rows in an index. If the GROUP BY clause has form:

    GROUP BY keyXpart1, keyXpart2, keyXpart3

    then we can use index statistics on keyX to find out number of distinct
    values. Note that we don't need to cover all key parts: for

    GROUP BY keyXpart3

    we can still index statistics on n_distinct(keyX, n_parts=3), although it
    would produce a (probably generous) upper bound.

    The above criteria handle the basic cases and are easy to check for.
    Feel free to come up with tighter bounds.

  @param
    join_output_card  Number of rows after join operation

  @return
    Number of rows that will be left after grouping operation
*/
double estimate_post_group_cardinality(JOIN *join, double join_output_card)
{
  Dynamic_array<Item*> group_cols(join->thd->mem_root);
  ORDER *cur_group;

  Json_writer_object wrapper(join->thd);
  Json_writer_object trace(join->thd, "materialized_output_cardinality");
  trace.add("join_output_card", join_output_card);

  /*
    Walk the GROUP BY list and put it into group_cols.

    Also check that each item depends on just one table.

    If there's an item that depends on multiple tables, we can't produce any
    estimate.
  */
  for (cur_group= join->group_list; cur_group; cur_group= cur_group->next)
  {
    Item *item= *cur_group->item;
    table_map map= item->used_tables();
    if ((map & PSEUDO_TABLE_BITS) || !has_one_bit_set(map))
    {
      /* Can't estimate */
      return join_output_card;
    }
    else
      group_cols.append(item);
  }
  group_cols.sort(cmp_items_by_used_tables);

  double new_card= 1.0;

  Item **pos= group_cols.front();

  while (pos != group_cols.end())
  {
    new_card *= estimate_table_group_cardinality(join, &pos, group_cols.end());

    if (new_card > join_output_card)
      return join_output_card;
  }

  trace.add("post_group_card", new_card);
  return new_card;
}

/*
  In the worst case, we get table's found_records.
*/

double estimate_table_group_cardinality(JOIN *join, Item ***group_list,
                                        Item* const *end)
{
  TABLE *table= NULL;
  key_map possible_keys;
  Dynamic_array<int> columns(join->thd->mem_root);
  double card=1.0;
  double table_records_after_where;

  table_map table_bit= (**group_list)->used_tables();
  /*
    join->map2table is not set yet, so find our table in JOIN_TABs.
  */
  for (JOIN_TAB *tab= join->join_tab;
       tab < join->join_tab + join->top_join_tab_count;
       tab++)
  {
    if (tab->table->map == table_bit)
    {
      table= tab->table;
      table_records_after_where= tab->found_records;
      break;
    }
  }

  possible_keys.clear_all();
  bool found_complex_item= false;

  /*
    Walk through the group list and collect fields.
    If there are other kinds of items, return table's cardinality.
  */
  Item **p;
  for (p= *group_list;
       p != end && (*p)->used_tables() == table_bit;
       p++)
  {
    Item *real= (*p)->real_item();
    if (real->type() == Item::FIELD_ITEM)
    {
      Field *field= ((Item_field*)real)->field;
      possible_keys.merge(field->part_of_key);
      columns.append(field->field_index);
    }
    else
      found_complex_item= true;
  }

  /* Tell the caller where group_list ended */
  *group_list= p;

  if (found_complex_item)
    goto whole_table;

  possible_keys.intersect(table->keys_in_use_for_query);
  /*
    Ok, group_list has only columns and we've got them in 'columns'.
  */
  while (!possible_keys.is_clear_all())
  {
    /* Find the index which has the longest prefix covered by columns. */
    const KEY *longest_key= NULL;
    int longest_len= 0;
    key_map::Iterator key_it(possible_keys);
    uint key;
    while ((key= key_it++) != key_map::Iterator::BITMAP_END)
    {
      const KEY *keyinfo= table->key_info + key;
      if (!keyinfo->actual_rec_per_key(0))
      {
        // No statistics => we can't use this index.
        possible_keys.clear_bit(key);
        continue;
      }

      int part;
      for (part= 0; part < (int)keyinfo->usable_key_parts; part++)
      {
        uint field_index= keyinfo->key_part[part].field->field_index;
        if (columns.find_first(field_index) == columns.NOT_FOUND)
          break;
      }

      if (part > 0)
      {
        if (part > longest_len)
        {
          longest_len= part;
          longest_key= keyinfo;
        }
      }
      else
        possible_keys.clear_bit(key);
    }

    if (longest_key)
    {
      const KEY *keyinfo= longest_key;

      // Multiply cardinality, remove the handled columns.
      double index_card= (rows2double(table->stat_records()) /
               keyinfo->actual_rec_per_key(longest_len-1));
      card *= index_card;
      if (card > table_records_after_where)
        goto whole_table;

      for (int part= 0; part < longest_len; part++)
      {
        uint field_index= keyinfo->key_part[part].field->field_index;
        size_t idx= columns.find_first(field_index);
        if (idx != columns.NOT_FOUND)
          columns.del(idx);
        else
          DBUG_ASSERT(0);
      }

      // If we've covered all fields, return.
      if (!columns.size())
        return card;
    }
    else
      break; // Couldn't use any indexes
  }

  /* Get cardinality from histogram data */
  for (size_t i=0; i < columns.size(); i++)
  {
    double freq;
    Field *field= table->field[columns.at(i)];
    if (!field->read_stats ||
        0.0 == (freq= field->read_stats->get_avg_frequency()))
      goto whole_table;
    card *= rows2double(table->stat_records()) / freq;
  }

  if (card < table_records_after_where)
    return card;

whole_table:
  return table_records_after_where;
}

