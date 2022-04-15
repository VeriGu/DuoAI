#ifndef STRINGPROCESSOR_H
#define STRINGPROCESSOR_H

#include <regex>
#include "basics.h"

#define INVALID_PREDICATE_COLUMN -1000

using std::regex; using std::regex_search; using std::smatch;

class StringProcessor
{
private:
	const Config& config;
	int num_types;
	vector<string> sketches;
	vector<vector<vector<int>>> sketches_holes_each_type;  // first index: sketch, second index: type, the inner vector<int> is the list of locations in the discretized representation
	map<string, int> sketch_index_map;
	map<vars_t, vector<vector<int>>> discretized_predicates_dict;
	map<inst_t, vector<vector<int>>> discretized_inst_predicates_dict;
	map<vars_t, map<vector<int>, int>> discretized_predicates_index_map_dict;
	map<inst_t, map<vector<int>, int>> discretized_inst_predicates_index_map_dict;
	void destruct_predicates_dict_core(const map<vars_t, vector<string>>& input_predicates_dict, map<vars_t, vector<vector<int>>>& output_discretized_predicates_dict, bool sketches_calculated);
	void reverse_indexing(const map<vars_t, vector<vector<int>>>& input_discretized_predicates_dict, map<vars_t, map<vector<int>, int>>& output_discretized_predicates_index_map);
public:
	StringProcessor(const Config& config_) : config(config_), num_types(0) {}
	void initialize();
	vector<vector<int>> get_discretized_predicates(const vars_t& vars) const;
	map<vector<int>, int> get_discretized_inst_predicates_index_map(const inst_t& inst) const;
	string parse_predicate_str(const string& predicate_str, vector<string>& predicate_args) const;
	int parse_predicate_term(const string& predicate_term, int expected_type, Term_Subtype& term_subtype, string& processed_term, vector<string>& function_args) const;
	void parse_predicate_into_rep(const string& predicate_str, PredicateRep& predicateRep) const;
	void parse_predicates(const vector<string>& predicates, map<string, vector<int>>& var_in_p, map<string, int>& p_to_idx) const;
	void remap_predicates(const vector<string>& old_predicates, const map<string, string>& vars_map, vector<string>& new_predicates) const;
	void column_compression(const inst_t& inst, const vector<string>& full_predicates, vector<string>& compressed_predicates);
	void reconstruct_var_group(const vars_t& vars, vector<vector<string>>& vars_grouped) const;
	void destruct_predicates_dict(const map<vars_t, vector<string>>& predicates_dict);
	void destruct_inst_predicates_dict(const map<vars_t, vector<string>>& inst_predicates_dict);
	int mapcall(const vars_t& vars, const inst_t& inst, const vector<int>& number_rep, const vector<vector<int>>& mapping_each_type);
	string get_sketch_by_id(int sketch_id);
	bool parse_inv_str(const string& inv_str_, vars_t& vars, qalter_t& qalter, vector<tuple<string, vector<string>, bool>>& inv_rep);
	string generate_new_inv_str(const vector<tuple<string, vector<string>, bool>>& inv_rep, const tuple<string, string, bool, bool>& transform);
	void add_checked_invs(vector<tuple<vars_t, qalter_t, string>>& output_vec_invs);
};

#endif
