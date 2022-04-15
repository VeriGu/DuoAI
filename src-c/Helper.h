#ifndef HELPER_H
#define HELPER_H

#include "basics.h"
#include "StringProcessor.h"

class Helper
{
private:
	const Config& config;
	const StringProcessor& processor;
public:
	Helper(const Config& config_, const StringProcessor& processor_) : config(config_), processor(processor_) {}
	void extract_exists_vars(const vars_t& vars, const qalter_t& qalter, map<int, int>& exists_type_to_varnum_map, vector<int>& exists_type_list, vector<string>& exists_vars, vector<int>& leading_forall_vars);
	bool bfs_check_connectivity(const vector<set<int>>& edges, const clause_t& candidate_clause, vector<clause_t>& connected_components);
	void calc_anded_clauses(int number_predicates, const map<string, vector<int>>& var_in_p, const vector<string>& exists_vars, vector<vector<clause_t>>& anded_clauses, vector<map<clause_t, vector<clause_t>>>& connected_components_dicts);
	void calc_vars_mapping(int type_index, int in_num, int out_num, bool is_unique_ordered, vector<map<string, string>>& vars_mappings);
	void calc_vars_self_mapping(int in_num, int out_num, vector<vector<int>>& vars_mappings);
	void update_base_implied_formulas_each_clause(const inv_t& base_inv, int number_predicates, unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause) const;
	void calc_base_implied_formulas_each_clause(int number_predicates, const inv_set_t& base_extended_invs, unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause);
	void remove_tautology_false_in_anded_clauses(vector<vector<clause_t>>& anded_clauses, int number_predicates, const inv_set_t& base_extended_invs);
	void sort_anded_clauses_by_base_implication(vector<vector<clause_t>>& anded_clauses, const unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause);
	void integrate_implied_ored_clauses(const unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause, const clause_t& anded_clause, unordered_set<vector<int>, VectorHash>& implied_ored_clauses) const;
	int check_if_clause_is_subset_of_any_clause_in_group(const clause_t& clause, const vector<clause_t>& clause_group);
	bool check_if_clause_can_reduce_clauses_in_group(const clause_t& clause, const vector<clause_t>& clause_group, int number_predicates, clause_t& final_witness, vector<clause_t>& clauses_to_remove);
	void calc_DE_simplified_dict(const vector<clause_t>& anded_clauses, const map<int, int>& exists_type_to_varnum_map, const vector<string>& predicates, const map<string, int>& p_to_idx, unordered_map<clause_t, clause_t, VectorHash>& DE_simplified_forms_dict);
	bool check_if_candidate_inv_is_tautology(const inv_t& candidate_inv, int number_predicates, unordered_map<inv_t, bool, SetVectorHash>& curr_checked_tautology_dict);
	bool check_if_inv_is_FOCAEI_redundant(const inv_t& candidate_inv, const inv_set_t& extended_invs, const inv_set_t& low_deuniqued_invs);
	bool check_if_inv_within_max_or_and_literal(const inv_t& candidate_inv) const;
	void generalize_invs(const inv_set_t& pred_extended_invs, const vector<vector<int>>& column_indices_list, inv_set_t& succ_extended_invs);
	void get_all_qalters(int num_types, vector<qalter_t>& all_qalters);
	void get_all_is_unique_ordereds(int num_types, vector<qalter_t>& all_is_unique_ordereds);
	void zip_merge_vector_of_map_string(const vector<map<string, string>>& vec_of_map_str_1, const vector<map<string, string>>& vec_of_map_str_2, vector<map<string, string>>& merged_vec_of_map_str);
};

#endif
