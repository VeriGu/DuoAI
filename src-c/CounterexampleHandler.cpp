#include "CounterexampleHandler.h"

void CounterexampleHandler::destruct_inst_predicates_dict()
{
	// predicate "hello(N1,E2)" will be destructed to a pair <"hello", ['0', '1']>
	for (map<inst_t, vector<string>>::const_iterator it = inst_predicates_dict.begin(); it != inst_predicates_dict.end(); it++)
	{
		const inst_t& inst = it->first;
		const vector<string>& predicates = it->second;
		for (const string& predicate_str : predicates)
		{
			PredicateRep predicateRep;
			processor.parse_predicate_into_rep(predicate_str, predicateRep);
			inst_predicateReps_dict[inst].push_back(predicateRep);
		}
	}
}

void CounterexampleHandler::print_data_mat(const DataMatrix& data_mat)
{
	int nrow = data_mat.nrow, ncol = data_mat.ncol;
	for (int row = 0; row < nrow; row++)
	{
		const int* data_line = data_mat.data_ptr[row];
		for (int col = 0; col < ncol; col++)
		{
			cout << data_line[col] << ' ';
		}
		cout << '\n';
	}
}

void CounterexampleHandler::parse_counterexample_lines(const vector<string>& counterexample_lines, vector<map<char, set<char>>>& le_maps, map<string, map<vector<char>, bool>>& relation_predicates_truth_map, map<string, char>& individual_map)
{
	assert(int(le_maps.size()) == num_types && relation_predicates_truth_map.empty() && individual_map.empty());
	for (const auto& amap : le_maps) assert(amap.empty());
	for (const string& line : counterexample_lines)
	{
		vector<string> equal_splitted;
		split_string(line, '=', equal_splitted);
		assert(equal_splitted.size() == 2);
		const string& first_str = equal_splitted[0];
		const string& second_str = equal_splitted[1];
		if (first_str[0] == '@')
		{
			// introduce an object (e.g., @N2 = 0). Ivy may not introduce all objects used. We do not use such a line
		}
		else
		{
			// a relation predicate, module relation predicate, individual, or function application
			int left_paren = first_str.find('(');
			if (left_paren == -1)  // individual
			{
				const string& individual_name = first_str;
				if (second_str == "true" || second_str == "false") throw not_implemented_exception("boolean individual in counterexample");
				assert(second_str.size() == 1);
				individual_map[individual_name] = second_str[0];
			}
			else
			{
				vector<string> comma_splitted;
				string relation_name = processor.parse_predicate_str(first_str, comma_splitted);
				vector<char> relation_args;
				for (const string& arg_str : comma_splitted)
				{
					assert(arg_str.size() == 1);
					char arg_char = arg_str[0];
					assert(arg_char >= '0' && arg_char <= '9');
					relation_args.push_back(arg_char);
				}
				if (second_str == "true" || second_str == "false")  // relation predicate or module relation predicate
				{
					bool predicate_is_true = second_str == "true";
					bool is_order_predicate = false;
					for (const auto& it : config.total_ordered_types)
					{
						int type_index = it.first;
						const string& order_relation = it.second;
						if (relation_name == order_relation)
						{
							// specify an order (e.g., le(1,0) = true), it may not be consistent with the natural order
							is_order_predicate = true;
							assert(relation_args.size() == 2);
							if (predicate_is_true)
							{
								le_maps[type_index][relation_args[0]].insert(relation_args[1]);
							}
							break;
						}
					}
					if (!is_order_predicate)  // general relation
					{
						relation_predicates_truth_map[relation_name][relation_args] = predicate_is_true;
					}
				}
				else  // function application
				{
					throw not_implemented_exception("Ivy function application in counterexample");
				}
			}
		}
	}
}

void CounterexampleHandler::calc_raw_to_ordered_maps(const vector<map<char, set<char>>>& le_maps, vector<map<char, char>>& raw_to_ordered_maps)
{
	assert(int(raw_to_ordered_maps.size()) == num_types);
	for (const auto& amap : raw_to_ordered_maps) assert(amap.empty());
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		if (le_maps[type_index].empty()) continue;
		// sort ordered objects
		const map<char, set<char>>& le_map = le_maps[type_index];
		int num_ordered_objs = le_map.size();
		vector<char> ordered_objs(num_ordered_objs);
		vector<bool> index_filled(num_ordered_objs, false);  // used in assertion that there is one and only one object with K objects greater or equal
		for (map<char, set<char>>::const_iterator it = le_map.begin(); it != le_map.end(); it++)
		{
			char obj = it->first;
			int greater_or_equal_obj_count = it->second.size();
			ordered_objs[num_ordered_objs - greater_or_equal_obj_count] = obj;
			assert(!index_filled[num_ordered_objs - greater_or_equal_obj_count]);
			index_filled[num_ordered_objs - greater_or_equal_obj_count] = true;
		}
		map<char, char> raw_to_ordered_map;  // if ordered_objs = ['2', '0', '1'], then raw_to_ordered_map = {'0': '1', '1': '2', '2': '0'}
		for (int i = 0; i < num_ordered_objs; i++) raw_to_ordered_map[ordered_objs[i]] = char(i) + '0';
		raw_to_ordered_maps[type_index] = raw_to_ordered_map;
	}
}

void CounterexampleHandler::reorder_variables_and_extract_inst_size(const vector<map<char, char>>& raw_to_ordered_maps, map<string, map<vector<char>, bool>>& relation_predicates_truth_map, map<string, char>& individual_map, inst_t& cte_inst_size)
{
	// check if relation_predicates is well formed, reorder if necessary, and extract the instance size of the counterexample
	cte_inst_size.clear();
	for (int i = 0; i < num_types; i++) cte_inst_size.push_back(0);
	for (auto& it : relation_predicates_truth_map)
	{
		const string& relation_name = it.first;
		assert(config.relations.find(relation_name) != config.relations.end());
		map<vector<char>, bool> new_predicates_map;  // after reordering
		for (auto const& sub_it : it.second)
		{
			const vector<char>& relation_args = sub_it.first;
			bool predicate_is_true = sub_it.second;
			const vector<int>& relation_signature = config.relations.at(relation_name);
			int num_args = relation_args.size();
			assert(num_args == int(relation_signature.size()));
			vector<char> reordered_args = relation_args;
			for (int i = 0; i < num_args; i++)
			{
				int arg_type = relation_signature[i];
				cte_inst_size[arg_type] = max2(cte_inst_size[arg_type], relation_args[i] - '0' + 1);
				if (config.total_ordered_types.find(arg_type) != config.total_ordered_types.end())
				{
					reordered_args[i] = raw_to_ordered_maps[arg_type].at(relation_args[i]);
				}
			}
			new_predicates_map[reordered_args] = predicate_is_true;
		}
		it.second = new_predicates_map;
	}
	for (auto& it : individual_map)
	{
		const string& individual_name = it.first;
		assert(config.individuals.find(individual_name) != config.individuals.end());
		int individual_type = config.individuals.at(individual_name);
		cte_inst_size[individual_type] = max2(cte_inst_size[individual_type], it.second - '0' + 1);
		if (config.total_ordered_types.find(individual_type) != config.total_ordered_types.end())
		{
			it.second = raw_to_ordered_maps[individual_type].at(it.second);
		}
	}
	for (int type_index = 0; type_index < num_types; type_index++) assert(cte_inst_size[type_index] > 0);  // every domain should have nonzero objects
}

void CounterexampleHandler::get_unbounded_relations(const map<string, map<vector<char>, bool>>& relation_predicates_truth_map, const inst_t& cte_inst_size, set<string>& unbounded_relations)
{
	assert(unbounded_relations.empty());
	for (map<string, vector<int>>::const_iterator it = config.relations.begin(); it != config.relations.end(); it++) unbounded_relations.insert(it->first);
	for (map<string, map<vector<char>, bool>>::const_iterator it = relation_predicates_truth_map.begin(); it != relation_predicates_truth_map.end(); it++)
	{
		const string& relation_name = it->first;
		unbounded_relations.erase(relation_name);
		int num_relation_args = it->second.size();
		int expected_num_relation_args = 1;
		for (int i = 0; i < int(config.relations.at(relation_name).size()); i++) expected_num_relation_args *= cte_inst_size[config.relations.at(relation_name)[i]];
		assert(num_relation_args == expected_num_relation_args);
	}
}

void CounterexampleHandler::parse_counterexample_lines_into_data_mat(const vector<string>& counterexample_lines, inst_t& cte_inst_size, DataMatrix& data_mat)
{
	vector<map<char, set<char>>> le_maps(num_types);  // first index: type index. For non-ordered types the map should be empty. Then le['1'] = {'0', '1'} means that le(1,0) = true, le(1,1) = true
	map<string, map<vector<char>, bool>> relation_predicates_truth_map;  // first index: relation name, second index: arguments (e.g., ['2', '0'])
	map<string, char> individual_map;  // first index: individual name, second index: which variable it equals (before sorting)
	parse_counterexample_lines(counterexample_lines, le_maps, relation_predicates_truth_map, individual_map);

	vector<map<char, char>> raw_to_ordered_maps(num_types);  // first index: type index. Then a map from unordered variable to its ordered position (starting from 0), e.g., if "EPOCH2" is the smallest epoch, then {'2'->'0', ...}
	calc_raw_to_ordered_maps(le_maps, raw_to_ordered_maps);
	reorder_variables_and_extract_inst_size(raw_to_ordered_maps, relation_predicates_truth_map, individual_map, cte_inst_size);
	set<string> unbounded_relations;  // the Ivy counterexample may not include predicates for every relation
	get_unbounded_relations(relation_predicates_truth_map, cte_inst_size, unbounded_relations);

	const vector<PredicateRep>& predicates = inst_predicateReps_dict.at(cte_inst_size);
	int number_predicates = predicates.size();
	vector<int> data_line(number_predicates, 0);
	vector<int> unbounded_columns;  // can be either 0 or 1
	for (int p_idx = 0; p_idx < number_predicates; p_idx++)
	{
		const PredicateRep& predicate = predicates[p_idx];
		if (predicate.predicate_type == Predicate_Type::le) throw not_implemented_exception("order predicate in csv");
		if (predicate.predicate_type == Predicate_Type::bool_idv) throw not_implemented_exception("boolean individual in csv");

		if (predicate.predicate_type == Predicate_Type::eq)
		{
			assert(predicate.term_subtypes.size() == 2 && predicate.terms.size() == 2);
			char lhs_rhs[2];
			bool idv_unbounded = false;
			for (int term_index = 0; term_index < 2; term_index++)
			{
				Term_Subtype subtype = predicate.term_subtypes[term_index];
				const string& term = predicate.terms[term_index];
				if (subtype == Term_Subtype::func) throw not_implemented_exception("function application in eq in csv");
				if (subtype == Term_Subtype::idv)
				{
					if (individual_map.find(term) == individual_map.end())
					{
						idv_unbounded = true;
						unbounded_columns.push_back(p_idx);
						break;
					}
					else
					{
						lhs_rhs[term_index] = individual_map.at(term);
					}
				}
				else if (subtype == Term_Subtype::qvar)
				{
					assert(term.size() == 1);
					lhs_rhs[term_index] = term[0];
				}
			}
			if (!idv_unbounded)
			{
				data_line[p_idx] = (lhs_rhs[0] == lhs_rhs[1]);
			}
		}
		else if (predicate.predicate_type == Predicate_Type::relation_p)
		{
			const string& relation_name = predicate.relation_name;
			if (unbounded_relations.find(relation_name) == unbounded_relations.end())
			{
				const map<vector<char>, bool>& predicates_map_this_relation = relation_predicates_truth_map.at(relation_name);
				int num_arg = predicate.terms.size();
				vector<char> restructored_args(num_arg);
				for (int arg_index = 0; arg_index < num_arg; arg_index++)
				{
					const string& relation_arg = predicate.terms[arg_index];
					if (predicate.term_subtypes[arg_index] != Term_Subtype::qvar) throw not_implemented_exception("relation has argument other than quantified variables");
					restructored_args[arg_index] = relation_arg[0];
				}
				bool predicate_is_true = predicates_map_this_relation.at(restructored_args);
				if (predicate_is_true) data_line[p_idx] = 1;
			}
			else
			{
				unbounded_columns.push_back(p_idx);
			}
		}
		else assert(false);
	}
	int num_unbounded_indices = unbounded_columns.size();
	if (num_unbounded_indices > 10) cout << "Warning! More than 10 unbounded predicates in the counterexample." << endl;
	int nrow = (1U << unbounded_columns.size());
	data_mat.nrow = nrow;
	data_mat.ncol = number_predicates;
	data_mat.data_ptr = contiguous_2d_array(nrow, data_mat.ncol);
	for (int row = 0; row < nrow; row++)
	{
		std::copy(data_line.begin(), data_line.end(), data_mat.data_ptr[row]);
		// use bitwise operation to decipher "row" to fill the unbounded values
		for (int i = 0; i < num_unbounded_indices; i++)
		{
			data_mat.data_ptr[row][unbounded_columns[i]] = (row >> i) & 1U;
		}
	}
	add_negation(data_mat);
	// print_data_mat(data_mat);  // print the counterexample as a 0/1 matrix on screen
}
