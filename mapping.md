| 旧定义/证明名称 (temp.v) | 新文件路径 | 新名称 (如有变动) | 备注 |
| :--- | :--- | :--- | :--- |
| **zeros** | - | - | 未在新文件中发现 |
| **nth_firstn** | Base/Positional.v | nth_firstn | |
| **nth_skipn** | - | - | 标准库自带或未显式迁移 |
| **skipn_firstn** | Base/Positional.v | skipn_firstn_comm | 功能一致 |
| **firstn_firstn** | Base/Positional.v | firstn_firstn | |
| **skipn_skipn** | Base/Positional.v | skipn_skipn | |
| **Znth** | Base/Positional.v | Znth | |
| **replace_nth** | Base/Positional.v | replace_nth | 参数顺序改为 (n l a) |
| **replace_Znth** | Base/Positional.v | replace_Znth | 参数顺序改为 (n l a) |
| **Znth0_cons** | Base/Positional.v | Znth0_cons | |
| **Znth_cons** | Base/Positional.v | Znth_cons | |
| **replace_Znth_cons** | Base/Positional.v | replace_Znth_cons | 参数顺序调整 |
| **replace_nth_app_l** | General/Length.v | replace_nth_app_l | |
| **replace_nth_app_r** | General/Length.v | replace_nth_app_r | |
| **replace_Znth_app_l** | General/Length.v | replace_Znth_app_l | |
| **replace_Znth_app_r** | General/Length.v | replace_Znth_app_r | |
| **replace_Znth_Znth** | Base/Positional.v | replace_Znth_Znth | 参数顺序调整 |
| **replace_Znth_nothing** | General/Length.v | replace_Znth_nothing | |
| **sublist (Definition)** | Base/Positional.v | Zsublist | Z版本更名为 Zsublist |
| **sublist_split_app_l** | General/Length.v | Zsublist_split_app_l | |
| **sublist_single** | General/Length.v | Zsublist_single | |
| **sublist_split** | General/Length.v | Zsublist_split | |
| **Zlength_nonneg** | General/Length.v | Zlength_nonneg | |
| **Zlength_app** | General/Length.v | Zlength_app | |
| **Zlength_app_cons** | General/Length.v | Zlength_app_cons | |
| **app_Znth1** | General/Length.v | app_Znth1 | |
| **app_Znth2** | General/Length.v | app_Znth2 | |
| **Znth_sublist** | General/Length.v | Znth_Zsublist | |
| **Znth_sublist0** | General/Length.v | Znth_Zsublist0 | |
| **Znth_indep** | General/Length.v | Znth_indep | |
| **Zlength_sublist** | General/Length.v | Zlength_Zsublist | |
| **Zlength_sublist0** | General/Length.v | Zlength_Zsublist0 | |
| **sublist_sublist** | Base/Positional.v | Zsublist_Zsublist | |
| **sublist_sublist0** | Base/Positional.v | Zsublist_Zsublist0 | |
| **sublist_sublist00** | Base/Positional.v | Zsublist_Zsublist00 | |
| **sublist_app_exact1** | General/Length.v | Zsublist_app_exact1 | |
| **sum** | - | - | 未在新文件中发现 |
| **sum_app** | - | - | 未在新文件中发现 |
| **sum_bound** | - | - | 未在新文件中发现 |
| **sum_bound_lt** | - | - | 未在新文件中发现 |
| **sublist_length** | General/Length.v | Zsublist_length | |
| **Znth_sublist_lt** | General/Length.v | Znth_Zsublist_lt | |
| **Znth_sublist_ge** | General/Length.v | Znth_Zsublist_ge | |
| **list_eq_ext** | General/Length.v | list_eq_ext | |
| **list_snoc_destruct** | Base/Inductive.v | list_snoc_destruct | |
| **sublist_nil** | Base/Positional.v | Zsublist_nil | |
| **sublist_of_nil** | Base/Positional.v | Zsublist_of_nil | |
| **sublist_self** | General/Length.v | Zsublist_self | |
| **Zlength_sublist'** | General/Length.v | Zlength_Zsublist' | |
| **sublist_split_app_r** | General/Length.v | Zsublist_split_app_r | |
| **sublist_cons1** | General/Length.v | Zsublist_cons1 | |
| **sublist_cons2** | General/Length.v | Zsublist_cons2 | |
| **interval_list** | ExListLib/InvertalList.v | interval_list | |
| **interval_list_valid1** | ExListLib/InvertalList.v | interval_list_bounded_lt | |
| **interval_list_valid2** | ExListLib/InvertalList.v | interval_list_NoDup | |
| **interval_list_valid3** | ExListLib/InvertalList.v | interval_list_bounded_le | |
| **Zlist_max** | - | - | 未在新文件中发现 |
| **interval_perm_keep** | ExListLib/InvertalList.v | interval_perm_keep | |
| **increasing** | ExListLib/InvertalList.v | Zincreasing | |
| **list_insert (Z)** | ExListLib/InvertalList.v | Zinsert | |
| **sort (Z)** | ExListLib/InvertalList.v | Zsort | |
| **list_insert_In** | ExListLib/InvertalList.v | Zinsert_In | |
| **sort_list_increasing** | ExListLib/InvertalList.v | Zsort_Zincreasing | |
| **list_insert_perm** | ExListLib/InvertalList.v | Zinsert_perm | |
| **sort_list_perm** | ExListLib/InvertalList.v | Zsort_perm | |
| **interval_list_compress** | ExListLib/InvertalList.v | interval_list_compress | |
| **increasing_interval_list_range** | ExListLib/InvertalList.v| increasing_interval_list_range | |
| **interval_list_range** | ExListLib/InvertalList.v | interval_list_range | |
| **Forall2** | General/Forall.v | Forall2 | |
| **Forall2_split** | General/Forall.v | Forall2_split | |
| **Forall2_split_app1** | General/Forall.v | Forall2_app_inv_l | 逻辑包含在 Forall2 库中 |
| **Forall2_split_app2** | General/Forall.v | Forall2_app_inv_r | 逻辑包含在 Forall2 库中 |
| **Forall2_merge** | General/Forall.v | Forall2_app | |
| **list_split_nth** | Base/Positional.v | firstn_skipSn | 更名为 firstn_skipSn |
| **Forall2_length** | General/Forall.v | Forall2_length | 使用标准库自带 |
| **Forall2_nth_iff** | General/Forall.v | Forall2_nth_iff | |
| **Forall2_app** | General/Forall.v | Forall2_app | |
| **Forall2_congr** | General/Forall.v | Forall2_congr | |
| **nperm** | ExListLib/Nperm.v | nperm | |
| **do_nperm** | ExListLib/Nperm.v | apply_perm | 更名为 apply_perm |
| **trivial_nperm** | ExListLib/Nperm.v | identity_perm | 更名为 identity_perm |
| **trivial_nperm_nperm** | ExListLib/Nperm.v | identity_perm_is_is_nperm | |
| **trivial_nperm_refl** | ExListLib/Nperm.v | identity_perm_refl | |
| **find_index** | ExListLib/Nperm.v | find_index | |
| **find_index_nth** | ExListLib/Nperm.v | find_index_nth | |
| **nth_find_index** | ExListLib/Nperm.v | nth_find_index | |
| **map_nth_len** | ExListLib/Nperm.v | map_nth_len | |
| **map_find_index_same** | ExListLib/Nperm.v | map_find_index_same | |
| **do_nperm_length** | ExListLib/Nperm.v | length_apply_perm | |
| **nperm_range** | ExListLib/Nperm.v | nperm_range | |
| **nperm_NoDup** | ExListLib/Nperm.v | nperm_NoDup | |
| **nperm_map** | ExListLib/Nperm.v | map_apply_perm | |
| **find_index_range** | ExListLib/Nperm.v | find_index_range | |
| **inverse_nperm** | ExListLib/Nperm.v | inverse_nperm | |
| **inverse_nperm_nperm** | ExListLib/Nperm.v | inverse_nperm_nperm | |
| **inverse_nperm_compose_refl1** | ExListLib/Nperm.v | apply_perm_inverse_l | |
| **inverse_nperm_compose_refl2** | ExListLib/Nperm.v | apply_perm_inverse_r | |
| **do_nperm_permutation** | ExListLib/Nperm.v | apply_perm_is_permutation | |
| **Forall2_nperm_congr0** | ExListLib/Nperm.v | Forall2_nperm_congr | |
| **Forall2_nperm_congr** | ExListLib/Nperm.v | Forall2_nperm_congr_iff | |
| **swap_nperm** | ExListLib/Nperm.v | swap_seq2 | |
| **swap_nperm_nperm** | ExListLib/Nperm.v | swap_seq2_is_nperm | |
| **swap_nperm_do_nperm** | ExListLib/Nperm.v | swap_nperm_apply_perm | |
| **list_swap_nperm** | ExListLib/Nperm.v | swap_seq | |
| **list_swap_nperm_nperm** | ExListLib/Nperm.v | swap_seq_is_nperm | |
| **list_swap_nperm_do_nperm** | ExListLib/Nperm.v | swap_seq_apply_perm | |
| **Forall2_map1** | General/Forall.v | Forall2_map1 | |
| **Forall2_map2** | General/Forall.v | Forall2_map2 | |
| **NoDup_map_fst** | - | - | 未在新文件中发现 |
| **Zseq** | - | - | 未在新文件中发现 |
| **list_insert (nat)** | - | - | 仅保留了 Z 版本的排序逻辑 |
| **sort (nat)** | - | - | 仅保留了 Z 版本的排序逻辑 |
| **list_update_nth** | - | - | 未在新文件中发现 |
| **list_eq_nth** | General/Length.v | list_eq_ext | 逻辑整合进 list_eq_ext |
| **Zseq_nth** | - | - | 未在新文件中发现 |
| **combine_skipn** | - | - | 未在新文件中发现 |
| **combine_app** | - | - | 未在新文件中发现 |
| **forall_in_cons** | General/Forall.v | Forall_in_cons | 命题结构有微调 |
| **forall_in_app** | - | - | 未在新文件中发现 |
| **prod_eq_dec** | - | - | 未在新文件中发现 |
| **list_eq_dec** | - | - | 未在新文件中发现 |
| **list_eqb** | - | - | 未在新文件中发现 |
| **option_eqb** | - | - | 未在新文件中发现 |
| **lift_option** | - | - | 未在新文件中发现 |
| **list_prod_split** | - | - | 未在新文件中发现 |
| **list_prod_merge** | - | - | 未在新文件中发现 |
| **factorial** | - | - | 未在新文件中发现 |
| **factorial_inc** | - | - | 未在新文件中发现 |