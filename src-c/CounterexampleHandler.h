#ifndef COUNTEREXAMPLEHANDLER_H
#define COUNTEREXAMPLEHANDLER_H

#include "preprocessing.h"
#include "StringProcessor.h"

class CounterexampleHandler
{
private:
	const StringProcessor& processor;
	const map<inst_t, vector<string>>& inst_predicates_dict;
	map<inst_t, vector<PredicateRep>> inst_predicateReps_dict;
	const Config& config;
	int num_types;
	void destruct_inst_predicates_dict();
	void print_data_mat(const DataMatrix& data_mat);
	void parse_counterexample_lines(const vector<string>& counterexample_lines, vector<map<char, set<char>>>& le_maps, map<string, map<vector<char>, bool>>& relation_predicates_truth_map, map<string, char>& individual_map);
	void calc_raw_to_ordered_maps(const vector<map<char, set<char>>>& le_maps, vector<map<char, char>>& raw_to_ordered_maps);
	void reorder_variables_and_extract_inst_size(const vector<map<char, char>>& raw_to_ordered_maps, map<string, map<vector<char>, bool>>& relation_predicates_truth_map, map<string, char>& individual_map, inst_t& cte_inst_size);
	void get_unbounded_relations(const map<string, map<vector<char>, bool>>& relation_predicates_truth_map, const inst_t& cte_inst_size, set<string>& unbounded_relations);
public:
	CounterexampleHandler(const StringProcessor& processor_, const map<inst_t, vector<string>>& solver_inst_predicates_dict, const Config& config_) : processor(processor_), inst_predicates_dict(solver_inst_predicates_dict), config(config_)
	{
		num_types = config.type_order.size();
		destruct_inst_predicates_dict();
	}
	void parse_counterexample_lines_into_data_mat(const vector<string>& counterexample_lines, inst_t& cte_inst_size, DataMatrix& data_mat);
};

#endif // COUNTEREXAMPLEHANDLER_H
