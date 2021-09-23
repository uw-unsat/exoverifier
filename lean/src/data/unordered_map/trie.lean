/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.trie.basic
import data.trie.instances

namespace trie

instance : generic_map pos_num trie :=
{ to_map := λ β,
  { to_list := to_list,
    nodupkeys := to_list_nodupkeys,

    elems := elems,
    mem_elems_iff := mem_elems_iff,

    empty := nil,
    empty_eq := rfl,

    null := null,
    null_iff := null_iff,

    unsingleton := unsingleton,
    unsingleton_iff := unsingleton_iff,

    card := card,
    card_eq := card_eq,

    lookup := λ _, lookup,
    mem_lookup_iff := λ _, by apply mem_lookup_iff,

    kinsert := λ _, kinsert,
    mem_kinsert_iff := λ _, by apply mem_kinsert_iff,

    insert₂ := λ _ _, by exactI insert₂,
    mem_insert₂_iff := λ _ _, by apply mem_insert₂_iff,

    insert_with := λ _, by exactI insert_with,

    kerase := λ _, kerase,
    mem_kerase_iff := λ _, by apply mem_kerase_iff,

    erase₂ := λ _ _, by exactI erase₂,
    mem_erase₂_iff := λ _ _, by apply mem_erase₂_iff,

    filter_map := filter_map,
    mem_filter_map_iff := mem_filter_map_iff,

    ksdiff := λ _, by exactI ksdiff,
    mem_ksdiff_iff := λ _, by apply mem_ksdiff_iff,

    union₂ := λ _ _, by exactI union₂,
    mem_union₂_iff := λ _ _, by apply mem_union₂_iff,

    sdiff₂ := λ _ _, by exactI sdiff₂,
    mem_sdiff₂_iff := λ _ _, by apply mem_sdiff₂_iff },

  to_traversable        := infer_instance,
  to_lawful_traversable := infer_instance,

  filter_map         := λ _ _, filter_map,
  mem_filter_map_iff := λ _ _, mem_filter_map_iff,

  filter_map₂         := λ _ _ _, filter_map₂,
  mem_filter_map₂_iff := λ _ _ _, mem_filter_map₂_iff }

end trie
