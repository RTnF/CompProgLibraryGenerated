import Proofs.Cpp.Gen.TreeMultiset
import Proofs.Cpp.TreeMultiset.ArenaCopy
import Proofs.Cpp.TreeMultiset.ArenaGrowth
import Proofs.Math.TreeMultiset.TreapHeap

namespace Proofs.Cpp.TreeMultiset

theorem construct_empty : type_of% @generated_init_spec := @generated_init_spec

theorem copy_preserves_contents : type_of% @generated_copy_spec := @generated_copy_spec

theorem move_transfers_contents : type_of% @generated_move_spec := @generated_move_spec

theorem priority_initial_state : type_of% @generated_priority_init := @generated_priority_init

theorem priority_step : type_of% @generated_next_priority := @generated_next_priority

theorem add_run : type_of% @generated_add_spec := @generated_add_spec

theorem remove_run : type_of% @generated_remove_count_spec := @generated_remove_count_spec

theorem remove_all_run : type_of% @generated_remove_all_spec := @generated_remove_all_spec

theorem size_run : type_of% @generated_size_spec := @generated_size_spec

theorem count_run : type_of% @generated_count_spec := @generated_count_spec

theorem enumerate_all_run : type_of% @generated_enumerate_all_spec := @generated_enumerate_all_spec

theorem enumerate_half_open_run : type_of% @generated_enumerate_spec := @generated_enumerate_spec

theorem min_run : type_of% @generated_min_spec := @generated_min_spec

theorem max_run : type_of% @generated_max_spec := @generated_max_spec

theorem kth_run : type_of% @generated_get_kth_spec := @generated_get_kth_spec

theorem rank_run : type_of% @generated_rank_spec := @generated_rank_spec

theorem rank_fits : type_of% @encodedRank_fits := @encodedRank_fits

theorem find_lower_run : type_of% @generated_find_lower_spec := @generated_find_lower_spec

theorem find_upper_run : type_of% @generated_find_upper_spec := @generated_find_upper_spec

theorem verify_run : type_of% @generated_verify_spec := @generated_verify_spec

theorem dump_run : type_of% @generated_aoj_dump_plan := @generated_aoj_dump_plan

theorem dump_sorted_keys : type_of% @public_print_keys := @public_print_keys

theorem dump_work : type_of% @generated_aoj_dump_work := @generated_aoj_dump_work

theorem insert_heap : type_of% @Tree.insert_heap := @Tree.insert_heap

theorem erase_heap : type_of% @Tree.erase_heap := @Tree.erase_heap

theorem height_le_distinct : type_of% @Tree.height_le_slots := @Tree.height_le_slots

theorem occupied_capacity_bound : type_of% @occupied_capacity := @occupied_capacity

theorem add_slot_growth : type_of% @generated_add_growth := @generated_add_growth

end Proofs.Cpp.TreeMultiset
