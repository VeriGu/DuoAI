#include "Solver.h"

Solver::Solver(string problem, int template_increase, int num_attempt, bool is_forall_only) : processor(config), helper(config, processor), encoder(config, processor)
{
	problem_name = problem;
	template_increase_times = template_increase;
	formula_size_increase_times = num_attempt;
	string csv_file_base = "../traces/" + problem + "_" + std::to_string(template_increase) + "/";
	string config_file = "../configs/" + problem + "_" + std::to_string(template_increase) + ".txt";
	config.max_literal = 0;
	config.max_exists = 0;
	config.max_ored_clauses = 0;
	config.max_anded_literals = 0;
	config.max_pos_exists = MAX_POS_EXISTS;
	config.one_to_one_exists = false;
	config.hard = false;
	read_config(config_file, &config);
	// round-robin template increase
	if (is_forall_only)
	{
		config.max_ored_clauses = config.max_ored_clauses + formula_size_increase_times;
		config.max_literal = config.max_literal + formula_size_increase_times;
		config.max_anded_literals = 1;
		config.max_exists = 0;
	}
	else
	{
		config.max_literal = config.max_literal + (formula_size_increase_times + 3) / 4;
		config.max_ored_clauses = config.max_ored_clauses + (formula_size_increase_times + 2) / 4;
		config.max_anded_literals = config.max_anded_literals + (formula_size_increase_times + 1) / 4;
		config.max_exists = config.max_exists + formula_size_increase_times / 4;
	}
	cout << "current formula size: max-literal=" << config.max_literal << ", max-ored-clauses=" << config.max_ored_clauses << ", max-anded-literals=" << config.max_anded_literals << ", max-exists=" << config.max_exists << ", template-increase=" << template_increase << endl;
	num_types = config.type_order.size();
	processor.initialize();
	forall_only_qalter = qalter_t(num_types, false);
	check_config_well_formed();
	for (const string& type_name : config.type_order)
	{
		template_sizes.push_back(config.template_vars_map[type_name].size());
	}
	for (const inst_t& curr_instance_size : config.instance_sizes)
	{
		string instance_size_str;
		for (int number : curr_instance_size)
		{
			instance_size_str += std::to_string(number) + "-";
		}
		instance_size_str.pop_back();
		string csv_file = csv_file_base + instance_size_str + ".csv";
		read_trace(csv_file, inst_predicates_dict[curr_instance_size], inst_data_mat_dict[curr_instance_size]);
		add_negation(inst_data_mat_dict[curr_instance_size]);
	}
	column_compression_on = false;
	py_column_compression_detected = false;
	input_ivy_file = "../protocols/" + problem + "/" + problem + ".ivy";
	default_output_ivy_inv_file = "../outputs/" + problem_name + "/" + problem_name + "_" + (is_forall_only ? "f" : "e") + std::to_string(template_increase) + "_inv" + ".ivy";
}

void Solver::check_config_well_formed() const
{
	assert(int(config.template_vars_map.size()) == num_types);
	assert(int(config.type_abbrs.size()) == num_types);
	for (const string& type_name : config.type_order)
	{
		assert(config.template_vars_map.find(type_name) != config.template_vars_map.end());
		assert(config.type_abbrs.find(type_name) != config.type_abbrs.end());
		const string& type_abbr = config.type_abbrs.at(type_name);
		const vector<string>& type_vars = config.template_vars_map.at(type_name);
		for (int i = 0; i < int(type_vars.size()); i++)
		{
			assert(type_vars[i] == type_abbr + std::to_string(i + 1));
		}
	}
}

void Solver::calc_predicates_dict()
{
	predicates_dict[template_sizes] = inst_predicates_dict[template_sizes];
	if (inst_predicates_dict[template_sizes].size() > COLUMN_COMPRESSION_THRESHOLD)
	{
		if (config.max_exists > 0)
		{
			column_compression_on = true;
			processor.column_compression(template_sizes, inst_predicates_dict.at(template_sizes), predicates_dict[template_sizes]);
		}
	}

	int total_num_predicates = predicates_dict[template_sizes].size();
	int num_optional_qauntified_variables = std::accumulate(template_sizes.begin(), template_sizes.end(), 0) - num_types;
	bool memory_explosion_expected = ((total_num_predicates > COLUMN_COMPRESSION_THRESHOLD) && (config.max_ored_clauses >= DISJ_STORE_CUTOFF_SIZE || num_optional_qauntified_variables >= OPTIONAL_QUANTIFIED_VARIABLE_CUTOFF_SIZE))
		|| ((total_num_predicates > COLUMN_COMPRESSION_THRESHOLD*3/4) && (config.max_ored_clauses > DISJ_STORE_CUTOFF_SIZE || num_optional_qauntified_variables > OPTIONAL_QUANTIFIED_VARIABLE_CUTOFF_SIZE));
	if (memory_explosion_expected)
	{
		cout << "Exiting for memory safety..." << endl;
		exit(-1);
	}
	if (predicates_dict.at(template_sizes).size() > BOUND_MAX_OR_COLUMN_THREDHOLD)
	{
		cout << "Too many predicates (" << predicates_dict.at(template_sizes).size() << ") that can appear in the invariants. Bounding initial max_ored_clauses to <=2." << endl;
		config.max_literal = min2(config.max_literal, 2);
	}

	for (int type_index = 0; type_index < num_types; type_index++)
	{
		const string& type_name = config.type_order[type_index];
		const vector<string>& curr_group = config.template_vars_map[type_name];
		map<vars_t, vector<string>> curr_predicates_dict = predicates_dict; // cannot reassign reference in C++
		for (int var_index = curr_group.size() - 1; var_index > 0; var_index--)
		{
			// TODO-long-term: support for one-to-one mapping
			map<vars_t, vector<string>> new_predicates_dict;
			for (map<vars_t, vector<string>>::iterator it = curr_predicates_dict.begin(); it != curr_predicates_dict.end(); it++)
			{
				const vars_t& vars = it->first;
				vector<string>& predicates = it->second;
				vector<string> new_predicates;
				reduce_predicates(predicates, new_predicates, type_index, var_index);
				vars_t new_vars = vars;
				new_vars[type_index]--;
				new_predicates_dict[new_vars] = new_predicates;
			}
			predicates_dict.insert(new_predicates_dict.begin(), new_predicates_dict.end());
			curr_predicates_dict = new_predicates_dict;
		}
	}

	if (config.one_to_one_exists)
	{
		vector<vars_t> vars_to_remove;
		for (const auto& it : predicates_dict)
		{
			const vars_t& vars = it.first;
			if (vars[config.one_to_one.in_type] != vars[config.one_to_one.out_type]) vars_to_remove.push_back(vars);
		}
		for (const vars_t& vars : vars_to_remove) predicates_dict.erase(vars);
	}

	// ensures that predicates_dict and inst_predicates_dict agree on the number of predicates for each variable set / instance size
	for (map<vars_t, vector<string>>::iterator it = predicates_dict.begin(); it != predicates_dict.end(); it++)
	{
		const vars_t& vars = it->first;
		const vector<string>& predicates = it->second;
		if (inst_predicates_dict.find(vars) != inst_predicates_dict.end())
		{
			if (column_compression_on)
			{
				assert(predicates.size() <= inst_predicates_dict[vars].size());
			}
			else
			{
				assert(predicates.size() == inst_predicates_dict[vars].size());
			}
		}
	}
}

void Solver::calc_varinp_and_ptoidx()
{
	for (map<vars_t, vector<string>>::iterator it = predicates_dict.begin(); it != predicates_dict.end(); it++)
	{
		const vars_t& vars = it->first;
		const vector<string>& predicates = it->second;
		map<string, vector<int>> var_in_p;
		map<string, int> p_to_idx;
		processor.parse_predicates(predicates, var_in_p, p_to_idx);
		var_in_p_dict[vars] = var_in_p;
		p_to_idx_dict[vars] = p_to_idx;
	}

	for (map<inst_t, vector<string>>::iterator it = inst_predicates_dict.begin(); it != inst_predicates_dict.end(); it++)
	{
		const inst_t& inst = it->first;
		const vector<string>& predicates = it->second;
		map<string, vector<int>> var_in_p;
		map<string, int> p_to_idx;
		processor.parse_predicates(predicates, var_in_p, p_to_idx);
		inst_var_in_p_dict[inst] = var_in_p;
		inst_p_to_idx_dict[inst] = p_to_idx;
	}
}

void Solver::calc_single_type_mappings()
{
	single_type_mappings.resize(num_types);
	vector<int> max_instance_each_type(num_types, 1);
	for (const inst_t& inst : config.instance_sizes)
	{
		for (int i = 0; i < num_types; i++)
		{
			if (inst[i] > max_instance_each_type[i]) max_instance_each_type[i] = inst[i];
		}
	}
	single_type_mappings.resize(num_types);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		int max_vars = template_sizes[type_index];
		int max_inst = max_instance_each_type[type_index];
		string type_abbr = config.type_abbrs[config.type_order[type_index]];
		single_type_mappings[type_index].resize(max_vars + 1);
		for (int i = 1; i <= max_vars; i++)
		{
			single_type_mappings[type_index][i].resize(max_inst + 1);
			for (int j = 1; j <= max_inst; j++)
			{
				vector<map<string, string>> vars_mappings_true;
				helper.calc_vars_mapping(type_index, i, j, true, vars_mappings_true);
				single_type_mappings[type_index][i][j][true] = vars_mappings_true;
				vector<map<string, string>> vars_mappings_false;
				helper.calc_vars_mapping(type_index, i, j, false, vars_mappings_false);
				single_type_mappings[type_index][i][j][false] = vars_mappings_false;
			}
		}
	}
}

void Solver::calc_single_type_self_mappings()
{
	single_type_self_mappings.resize(num_types);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		int max_vars = template_sizes[type_index];
		string type_abbr = config.type_abbrs[config.type_order[type_index]];
		single_type_self_mappings[type_index].resize(max_vars + 1);
		for (int i = 1; i <= max_vars; i++)
		{
			single_type_self_mappings[type_index][i].resize(max_vars + 1);
			for (int j = 1; j <= i; j++)
			{
				vector<vector<int>> vars_mappings;
				helper.calc_vars_self_mapping(i, j, vars_mappings);
				single_type_self_mappings[type_index][i][j] = vars_mappings;
			}
		}
	}
}

void Solver::calc_column_indices_dict()
{
	processor.destruct_inst_predicates_dict(inst_predicates_dict);
	processor.destruct_predicates_dict(predicates_dict);
	int counter1 = 0, counter2 = 0, counter3 = 0;
	bool asymmetric_relation_warning_sent = false;
	for (const auto& it1 : predicates_dict)
	{
		const vars_t& vars = it1.first;
		// cout << "vars: " << vec_to_str(vars) << endl;
		const vector<vector<int>>& discretized_predicates = processor.get_discretized_predicates(vars);
		int number_predicates = discretized_predicates.size();
		for (const auto& it2 : inst_predicates_dict)
		{
			counter1++;
			const inst_t& inst = it2.first;
			// cout << "inst: " << vec_to_str(inst) << endl;
			const map<vector<int>, int> discretized_inst_predicates_index_map = processor.get_discretized_inst_predicates_index_map(inst);
			int number_inst_predicates = discretized_inst_predicates_index_map.size();
			vector<vector<bool>> all_is_unique_ordereds;
			helper.get_all_is_unique_ordereds(num_types, all_is_unique_ordereds);
			for (const vector<bool>& is_unique_ordered : all_is_unique_ordereds)
			{
				counter2++;
				// reconstruct single_type_mappings using vector of ints instead of map of strings
				vector<vector<vector<int>>> vectorized_mapping_list_each_type;
				for (int i = 0; i < num_types; i++)
				{
					// further optimization possible (get rid of strings)
					const vector<map<string, string>>& this_type_mapping_list = single_type_mappings[i][vars[i]][inst[i]][is_unique_ordered[i]];
					vector<vector<int>> vectorized_mapping_list;
					for (const map<string, string>& this_type_mapping : this_type_mapping_list)
					{
						assert(int(this_type_mapping.size()) == vars[i]);
						vector<int> vectorized_mapping(vars[i] + 1);
						for (const auto& it : this_type_mapping)
						{
							vectorized_mapping[*(it.first.end() - 1) - '0'] = *(it.second.end() - 1) - '0';
						}
						vectorized_mapping_list.push_back(vectorized_mapping);
					}
					vectorized_mapping_list_each_type.push_back(vectorized_mapping_list);
				}

				vector<int> vars_mappings_size_each_type;
				long long total_num_mappings = 1;
				for (int i = 0; i < num_types; i++)
				{
					int vars_mappings_size_this_type = single_type_mappings[i][vars[i]][inst[i]][is_unique_ordered[i]].size();
					vars_mappings_size_each_type.push_back(vars_mappings_size_this_type);
					total_num_mappings *= vars_mappings_size_this_type;
				}
				// loop over each global variable mapping (e.g., N1 -> N2, N2 -> N2, T1 -> T1)
				for (long long index_number = 0; index_number < total_num_mappings; index_number++)
				{
					counter3++;
					vector<int> mapping_indices_each_type(num_types);
					long long q = index_number;
					for (int i = num_types-1; i >= 0; i--)
					{
						mapping_indices_each_type[i] = q % vars_mappings_size_each_type[i];
						q = q / vars_mappings_size_each_type[i];
					}
					if (config.one_to_one_exists && mapping_indices_each_type[config.one_to_one.in_type] != mapping_indices_each_type[config.one_to_one.out_type]) continue;
					vector<vector<int>> mapping_each_type;
					for (int type_index = 0; type_index < num_types; type_index++)
					{
						int mapping_index = mapping_indices_each_type[type_index];
						mapping_each_type.push_back(vectorized_mapping_list_each_type[type_index][mapping_index]);
					}

					// codes below calculate column_indices_dict[vars][inst][is_unique_ordered][mapping_indices_each_type]
					vector<int> column_indices;
					column_indices.reserve(number_predicates * 2);
					for (const vector<int>& discretized_p : discretized_predicates)
					{
						int remapped_predicate_index = processor.mapcall(vars, inst, discretized_p, mapping_each_type);
						if (remapped_predicate_index == INVALID_PREDICATE_COLUMN && !column_compression_on && !asymmetric_relation_warning_sent)
						{
							cout << "Warning! Asymmetric predicate group " << processor.get_sketch_by_id(discretized_p[0]) << " found in samples" << endl;
							py_column_compression_detected = true;
							asymmetric_relation_warning_sent = true;
						}
						column_indices.push_back(remapped_predicate_index);
					}
					for (int i = 0; i < number_predicates; i++)
					{
						column_indices.push_back(column_indices[i] + number_inst_predicates);
					}
					column_indices_dict[vars][inst][is_unique_ordered][mapping_indices_each_type] = column_indices;
				}
			}
		}
	}
}

void Solver::calc_highlowvars_column_indices_dict()
{
	for (const vars_t& high_vars : vars_traversal_order)
	{
		for (const vars_t& low_vars : vars_traversal_order)
		{
			bool is_valid_subset = true;
			for (int type_index = 0; type_index < num_types; type_index++)
			{
				if (high_vars[type_index] < low_vars[type_index])
				{
					is_valid_subset = false;
					break;
				}
			}
			if (is_valid_subset)
			{
				const vector<string>& high_predicates = predicates_dict[high_vars];
				const map<string, int>& low_p_to_idx = p_to_idx_dict[low_vars];
				int num_high_predicates = high_predicates.size();
				int num_low_predicates = predicates_dict[low_vars].size();
				vector<int> high_to_low_mapping(2*num_high_predicates);
				for (int i = 0; i < num_high_predicates; i++)
				{
					const string& high_predicate = high_predicates[i];
					if (low_p_to_idx.find(high_predicate) != low_p_to_idx.end())
					{
						int index_in_low_predicates = low_p_to_idx.at(high_predicate);
						high_to_low_mapping[i] = index_in_low_predicates;
						high_to_low_mapping[i + num_high_predicates] = index_in_low_predicates + num_low_predicates;
					}
					else
					{
						high_to_low_mapping[i] = INVALID_PREDICATE_COLUMN;
						high_to_low_mapping[i + num_high_predicates] = INVALID_PREDICATE_COLUMN;
					}
				}
				highlowvars_column_indices_dict[high_vars][low_vars] = high_to_low_mapping;
			}
		}
	}
}

void Solver::calc_lowhighvars_column_indices_dict()
{
	// compared with column_indices_dict, which connects predicates_dict.at(vars) to csv columns of various instance sizes and is used to check candidate invariants on data matrices
	// lowhighvars_column_indices_dict connects predicates.at(vars) to predicates.at(higher_vars) at various types/dimensions and is used to project candidate invariants to larger quantifier prefix
	for (const vars_t & low_vars : vars_traversal_order)
	{
		const vector<string>& lower_predicates = predicates_dict[low_vars];
		int num_lower_predicates = lower_predicates.size();
		for (int type_index = 0; type_index < num_types; type_index++)
		{
			vars_t high_vars = low_vars;
			high_vars[type_index]++;
			if (config.one_to_one_exists && config.one_to_one.in_type == type_index) high_vars[config.one_to_one.out_type]++;
			if (std::find(vars_traversal_order.begin(), vars_traversal_order.end(), high_vars) != vars_traversal_order.end())
			{
				// a valid low-high vars pair, e.g., [2,1,1] - [2,1,2]
				const vector<string>& higher_predicates = predicates_dict[high_vars];
				int num_higher_predicates = higher_predicates.size();
				const map<string, int>& higher_p_to_idx = p_to_idx_dict[high_vars];
				vector<vector<bool>> all_is_unique_ordereds;
				helper.get_all_is_unique_ordereds(num_types, all_is_unique_ordereds);
				for (const vector<bool>& is_unique_ordered : all_is_unique_ordereds)
				{
					vector<vector<map<string, string>>> all_type_mappings;
					for (int type_index = 0; type_index < num_types; type_index++)
					{
						const vector<map<string, string>>& this_type_mappings = single_type_mappings[type_index][low_vars[type_index]][high_vars[type_index]][is_unique_ordered[type_index]];
						all_type_mappings.push_back(this_type_mappings);
						if (config.one_to_one_exists && config.one_to_one.out_type == type_index)
						{
							vector<map<string, string>> out_type_mappings = all_type_mappings.back();
							all_type_mappings.pop_back();
							vector<map<string, string>> in_type_mappings = all_type_mappings.back();
							all_type_mappings.pop_back();
							vector<map<string, string>> bijection_type_mappings;
							helper.zip_merge_vector_of_map_string(in_type_mappings, out_type_mappings, bijection_type_mappings);
							all_type_mappings.push_back(bijection_type_mappings);
						}
					}
					vector<vector<map<string, string>>> mapping_each_type_list_list = cart_product(all_type_mappings);
					vector<vector<int>> all_column_indices_this_lowhighvars_isuniqueordered;
					for (const vector<map<string, string>>& mapping_each_type_list : mapping_each_type_list_list)
					{
						map<string, string> vars_map;
						join_vector_of_maps(mapping_each_type_list, vars_map);
						vector<string> mapped_predicates;
						processor.remap_predicates(lower_predicates, vars_map, mapped_predicates);
						vector<int> column_indices(2 * num_lower_predicates);
						for (int i = 0; i < num_lower_predicates; i++)
						{
							int new_pos;
							if (higher_p_to_idx.find(mapped_predicates[i]) == higher_p_to_idx.end())
							{
								assert(column_compression_on || py_column_compression_detected);
								new_pos = INVALID_PREDICATE_COLUMN;  // negative number means no mapped predicate at higher vars
							}
							else
							{
								new_pos = higher_p_to_idx.at(mapped_predicates[i]);
							}
							column_indices[i] = new_pos;
							column_indices[i + num_lower_predicates] = new_pos + num_higher_predicates;
						}
						all_column_indices_this_lowhighvars_isuniqueordered.push_back(column_indices);
					}
					lowhighvars_column_indices_dict[low_vars][high_vars][is_unique_ordered] = all_column_indices_this_lowhighvars_isuniqueordered;
				}
			}
		}
	}
}

void Solver::calc_inst_data_mat_dict_each_leading_forall()
{
	// data projection
	// let's say we have three types T1 T2 T3. The template size is (2,2,1). The instance sizes are (1,1,1) - (3,3,3).
	inst_data_mat_dict_each_leading_forall[lead_forall_vars_t()] = inst_data_mat_dict;  // base case. No leading forall. Use csv files themselves
	vector<vector<lead_forall_vars_t>> leading_forall_vars_each_length(num_types + 1);  
	leading_forall_vars_each_length[0] = { lead_forall_vars_t() };
	// leading_forall_vars_each_length[0] = [ vector<int>() ]
	// leading_forall_vars_each_length[1] = [ [1], [2] ]
	// leading_forall_vars_each_length[2] = [ [1,1], [1,2], [2,1], [2,2] ]
	// leading_forall_vars_each_length[3] = [ [1,1,1], [1,2,1], [2,1,1], [2,2,1] ]
	// in other words, leading_forall_vars_each_length contains all possible leading forall variable numbers, which is the set of keys of inst_data_mat_dict_each_leading_forall
	for (int projecting_type_index = 0; projecting_type_index < num_types; projecting_type_index++)
	{
		if (config.one_to_one_exists && config.one_to_one.in_type == projecting_type_index) continue;
		// let's say we are now projecting T2, then projecting_type_index = 1. Before T2 the leading forall vars has two choices [1] and [2], 
		// T2 has only two var number choices 1 and 2, so we end up with 2*2=4 leading forall vars choices [1,1], [1,2], [2,1], [2,2] to be projected into
		int max_vars = config.template_vars_map[config.type_order[projecting_type_index]].size();  // how many quantified variables this type can have
		const vector<lead_forall_vars_t>& all_existing_leading_forall_vars = (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index) ? leading_forall_vars_each_length[projecting_type_index - 1] : leading_forall_vars_each_length[projecting_type_index];
		for (const lead_forall_vars_t& existing_leading_forall_vars : all_existing_leading_forall_vars)
		{
			const map<inst_t, DataMatrix>& last_data_mat_dict = inst_data_mat_dict_each_leading_forall.at(existing_leading_forall_vars);
			for (int num_vars = max_vars; num_vars >= 1; num_vars--)
			{
				// let's say we are projecting into leading forall vars [1,2]
				// last_data_mat_dict has 9 keys: [1,1,1], [1,1,2], ..., [1,3,2], [1,3,3]
				// we should discard [1,1,1], [1,1,2] and [1,1,3] because they cannot be mapped to two unique T2 quantified variables
				// new_data_mat_dict and deduplicated_data_mat_dict both should have three keys [1,2,1], [1,2,2], [1,2,3], each integrating two last keys. For example, [1,2,3] integrates last instance sizes [1,2,3] and [1,3,3]
				lead_forall_vars_t new_leading_forall_vars = existing_leading_forall_vars;
				new_leading_forall_vars.push_back(num_vars);
				if (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index) new_leading_forall_vars.push_back(num_vars);
				leading_forall_vars_each_length[projecting_type_index + 1].push_back(new_leading_forall_vars);  // add [1,2]
				map<inst_t, DataMatrix> new_data_mat_dict;
				map<inst_t, unordered_set<vector<int>, VectorHash>> deduplicated_data_mat_dict;
				for (map<inst_t, DataMatrix>::const_iterator it = last_data_mat_dict.begin(); it != last_data_mat_dict.end(); it++)
				{
					const inst_t& old_inst = it->first;
					int num_objects = old_inst[projecting_type_index];
					if (num_objects < num_vars) continue;  // discard [1,1,3]
					inst_t reduced_inst = old_inst;
					reduced_inst[projecting_type_index] = num_vars;
					if (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index) reduced_inst[projecting_type_index - 1] = num_vars;
					unordered_set<vector<int>, VectorHash>& deduplicated_data_mat = deduplicated_data_mat_dict[reduced_inst];  // deduplicated_data_mat may be not empty now, because multiple old_inst can project to the same reduced_inst
					const DataMatrix& old_data_mat = it->second;
					const map<string, int>& old_inst_p_to_idx = inst_p_to_idx_dict.at(old_inst);
					vector<map<string, string>> vars_mappings = single_type_mappings[projecting_type_index][num_vars][num_objects][true];
					if (config.one_to_one_exists && config.one_to_one.out_type == projecting_type_index)
					{
						const vector<map<string, string>>& in_type_vars_mappings = single_type_mappings[projecting_type_index - 1][num_vars][num_objects][true];
						vector<map<string, string>> bijection_vars_mappings;
						helper.zip_merge_vector_of_map_string(in_type_vars_mappings, vars_mappings, bijection_vars_mappings);
						vars_mappings = bijection_vars_mappings;
					}
					int num_predicates_old_inst = inst_predicates_dict.at(old_inst).size();
					int num_predicates_reduced_inst = inst_predicates_dict.at(reduced_inst).size();
					for (const map<string, string>& vars_map : vars_mappings)
					{
						vector<string> mapped_inst_predicates;
						processor.remap_predicates(inst_predicates_dict.at(reduced_inst), vars_map, mapped_inst_predicates);
						vector<int> column_indices(2 * num_predicates_reduced_inst);
						bool all_remapped_predicates_exists = true;
						for (int i = 0; i < num_predicates_reduced_inst; i++)
						{
							const string& mapped_p_str = mapped_inst_predicates[i];
							if (old_inst_p_to_idx.find(mapped_p_str) == old_inst_p_to_idx.end())
							{
								assert(column_compression_on || py_column_compression_detected);
								all_remapped_predicates_exists = false;
								break;
							}
							int new_pos = old_inst_p_to_idx.at(mapped_p_str);
							column_indices[i] = new_pos;
							column_indices[i + num_predicates_reduced_inst] = new_pos < num_predicates_old_inst? new_pos + num_predicates_old_inst : new_pos - num_predicates_old_inst;
						}
						if (!all_remapped_predicates_exists) continue;

						for (int i = 0; i < old_data_mat.nrow; i++)
						{
							int* row = old_data_mat.data_ptr[i];
							vector<int> reduced_row(2 * num_predicates_reduced_inst);
							int k = 0;
							for (int idx : column_indices)
							{
								reduced_row[k++] = row[idx];
							}
							deduplicated_data_mat.insert(reduced_row);
						}
					}
				}
				// now we have visited all old instances. We should convert deduplicated_data_mat_dict to new_data_mat_dict
				for (map<inst_t, unordered_set<vector<int>, VectorHash>>::const_iterator it = deduplicated_data_mat_dict.begin(); it != deduplicated_data_mat_dict.end(); it++)
				{
					const inst_t& inst = it->first;
					const unordered_set<vector<int>, VectorHash>& deduplicated_data_mat = it->second;
					int nrow = deduplicated_data_mat.size();
					if (nrow == 0) continue;
					int ncol = (*deduplicated_data_mat.begin()).size();
					assert(ncol > 0);
					DataMatrix new_data_mat;
					new_data_mat.data_ptr = contiguous_2d_array(nrow, ncol);
					new_data_mat.nrow = nrow;
					new_data_mat.ncol = ncol;
					int row_count = 0;
					for (const vector<int>& row : deduplicated_data_mat)
					{
						std::copy(row.begin(), row.end(), new_data_mat.data_ptr[row_count]);
						row_count++;
					}
					new_data_mat_dict[inst] = new_data_mat;
				}

				inst_data_mat_dict_each_leading_forall[new_leading_forall_vars] = new_data_mat_dict;
			}
		}
	}
}

void Solver::precompute_vars_self_mapping_bulk()
{
	for (int num_exists = 0; num_exists <= config.max_exists; num_exists++)
	{
		// iterate through each subtemplate and enumerate candidate invariants
		for (const vars_t& vars : vars_traversal_order)
		{
			for (const qalter_t& qalter : vars_qalter_exists_number[vars][num_exists])
			{
				precompute_vars_self_mapping(vars, qalter);
			}
		}
	}
}

void Solver::reduce_predicates(vector<string>& old_predicates, vector<string>& new_predicates, int type_index, int var_index_to_remove) const
{
	assert(new_predicates.size() == 0);
	map<string, vector<int>> var_in_p;
	map<string, int> p_to_idx;
	processor.parse_predicates(old_predicates, var_in_p, p_to_idx);
	int num_predicates = old_predicates.size();
	string var_to_remove = config.template_vars_map.at(config.type_order[type_index])[var_index_to_remove];
	vector<int> p_to_remove = var_in_p[var_to_remove];
	/* TODO-long-term: support one-to-one, below shows old code
	if (config.one_to_one_exists)
	{
		map<string, string>::iterator it = config.one_to_one_bidir.find(var_to_remove);
		if (it != config.one_to_one_bidir.end())
		{
			vector<int>& additional_p_to_remove = var_in_p[it->second];
			p_to_remove.insert(p_to_remove.end(), additional_p_to_remove.begin(), additional_p_to_remove.end());
		}
	}
	*/
	for (int i = 0; i < num_predicates; i++)
	{
		if (std::find(p_to_remove.begin(), p_to_remove.end(), i) == p_to_remove.end())
		{
			new_predicates.push_back(old_predicates[i]);
		}
	}
}

void Solver::calc_vars_traversal_order()
{
	vars_t genesis_vars(num_types, 1);
	vars_traversal_order.push_back(genesis_vars);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		vector<vars_t> curr_traversal_order = vars_traversal_order;
		int curr_group_size = template_sizes[type_index];
		for (int j = 1; j < curr_group_size; j++)
		{
			vector<vars_t> new_traversal_order;
			for (const vars_t& vars : curr_traversal_order)
			{
				vars_t new_vars = vars;
				new_vars[type_index]++;
				new_traversal_order.push_back(new_vars);
			}
			vars_traversal_order.insert(vars_traversal_order.end(), new_traversal_order.begin(), new_traversal_order.end());
			curr_traversal_order = new_traversal_order;
		}
	}
	if (config.one_to_one_exists)
	{
		vector<vars_t> filtered_vars_traversal_order;
		for (const vars_t& vars : vars_traversal_order)
		{
			if (vars[config.one_to_one.in_type] == vars[config.one_to_one.out_type]) filtered_vars_traversal_order.push_back(vars);
		}
		vars_traversal_order = filtered_vars_traversal_order;
	}
}

void Solver::calc_vars_qalters_exists_number()
{
	// enumerate all qalters
	vector<qalter_t> all_qalters;
	helper.get_all_qalters(num_types, all_qalters);
	// loop over each vars and qalter
	for (const vars_t& vars : vars_traversal_order)
	{
		vars_qalter_exists_number[vars].resize(config.max_exists + 1);
		for (const qalter_t& qalter : all_qalters)
		{
			int number_exists = 0;
			for (int i = 0; i < num_types; i++)
			{
				if (qalter[i]) number_exists += vars[i];
			}
			if (number_exists <= config.max_exists)
			{
				vars_qalter_exists_number[vars][number_exists].push_back(qalter);
			}
		}
	}
}

void Solver::enumerate_dnf(const vars_t& vars, const qalter_t& qalter, inv_set_t& inv_results, inv_set_t& extended_invs)
{
	// vars specifies the number of quantified variables for each type, qalter specifies for each type, whether the variables are universally or existentially quantified
	// preparation steps
	auto enumerate_dnf_start_time = time_now();
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	const vector<string>& predicates = predicates_dict[vars];
	int number_predicates = predicates.size();
	const map<string, vector<int>>& var_in_p = var_in_p_dict[vars];
	map<int, int> exists_type_to_varnum_map;
	vector<int> exists_type_list;
	vector<string> exists_vars;
	vector<int> leading_forall_vars;
	helper.extract_exists_vars(vars, qalter, exists_type_to_varnum_map, exists_type_list, exists_vars, leading_forall_vars);
	vector<vector<clause_t>> anded_clauses_with_redundancy; // ANDed terms that can appear in a nondecomposable DNF formula, first index is number of literals
	helper.calc_anded_clauses(number_predicates, var_in_p, exists_vars, anded_clauses_with_redundancy, connected_components_dict_dict[vars][qalter]);
	vector<vector<clause_t>> anded_clauses;  // ANDed terms without redundancy, if forall ... p /\ q -> r, then p /\ q /\ r is an in-clause-implication (ICI) redundant clause because r can be ommited
	if (exists_vars.size() == 0) anded_clauses = anded_clauses_with_redundancy;
	else remove_redundancy_in_anded_literal(vars, is_unique_ordered, anded_clauses_with_redundancy, anded_clauses);

	// this section is dedicated to PQR redundant form
	// if we replace all exists in template A with forall and get template B, we call B the "base subtemplate" of A. e.g., forall X1 forall Y1 Y2 is the base of forall X1 exists Y1 Y2; forall X1 < X2 forall Y1 < Y2 is the base of itself
	// successors_at_base_each_anded_clause: key: an anded clause p1 /\ ... /\ pm, value: a set of disjuncted literals, let's say q1 \/ ... \/ qn is an element, then in the base template, ~p1 \/ ... \/ pm \/ q1 \/ ... \/ qn is an invariant
	inv_set_t& base_extended_invs = exists_type_list.size() > 0 ? deuniqued_extended_invs_dict.at(vars).at(forall_only_qalter)[exists_type_list[0]] : extended_invs;
	unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash> base_implied_formulas_each_clause;
	helper.calc_base_implied_formulas_each_clause(number_predicates, base_extended_invs, base_implied_formulas_each_clause);
	helper.remove_tautology_false_in_anded_clauses(anded_clauses, number_predicates, base_extended_invs);  // if forall X. p(X) \/ q(X) is an invariant, then anded clause ~p(X) /\ ~q(X) should not be considered because it is always false
	// if (vars == vars_t({ 2 }) && qalter == qalter_t({ false })) for (int i = 0; i < number_predicates; i++) cout << i << ": " << predicates[i] << endl;  // for debug
	// if (vars == vars_t({ 2 }) && qalter == qalter_t({ false })) cout << "{ {2}, {27} } in extended_inv? " << (extended_invs.find(inv_t({ {2}, {27} })) != extended_invs.end()) << endl;  // for debug
	helper.sort_anded_clauses_by_base_implication(anded_clauses, base_implied_formulas_each_clause);

	vector<vector<vector<vector<clause_t>>>> anded_clause_combs(config.max_anded_literals + 1);
	bool tautology_DE_is_possible = false;  // double existential (DE) tautology: exists X1 X2. p(X1) \/ ~p(X2)
	for (map<int, int>::const_iterator it = exists_type_to_varnum_map.begin(); it != exists_type_to_varnum_map.end(); it++) if (it->second >= 2) tautology_DE_is_possible = true;
	vector<unordered_map<clause_t, clause_t, VectorHash>> DE_simplified_forms_dicts(config.max_anded_literals + 1);

	for (int num_literal_one_clause = 1; num_literal_one_clause <= config.max_anded_literals; num_literal_one_clause++)
	{
		int max_clauses_this_literal_number = min2(config.max_literal / num_literal_one_clause, config.max_ored_clauses);
		anded_clause_combs[num_literal_one_clause].resize(max_clauses_this_literal_number + 1);
		for (int num_clauses_this_literal_number = 1; num_clauses_this_literal_number <= max_clauses_this_literal_number; num_clauses_this_literal_number++)
		{
			vector<vector<clause_t>> anded_clause_combs_this_literal_and_clause_number;
			if (int(anded_clauses[num_literal_one_clause].size()) >= num_clauses_this_literal_number)
			{
				calc_combinations(anded_clauses[num_literal_one_clause], num_clauses_this_literal_number, anded_clause_combs_this_literal_and_clause_number);
				anded_clause_combs[num_literal_one_clause][num_clauses_this_literal_number] = anded_clause_combs_this_literal_and_clause_number;
			}
		}
		if (tautology_DE_is_possible) helper.calc_DE_simplified_dict(anded_clauses[num_literal_one_clause], exists_type_to_varnum_map, predicates, p_to_idx_dict.at(vars), DE_simplified_forms_dicts[num_literal_one_clause]);
	}

	// main enumeration loops
	for (int num_or = 1; num_or <= config.max_ored_clauses; num_or++)
	{
		for (int num_literal = config.max_literal; num_literal >= num_or; num_literal--)
		{
			// put num_literal balls into num_or buckets, at least one ball per bucket, number of balls non-decreasing from first to last bucket
			const vector<vector<int>>& ways_to_split = n_into_k[num_literal][num_or];
			bool time_for_space_highest_or = num_or >= DISJ_STORE_CUTOFF_SIZE && num_or == config.max_ored_clauses;
			if (time_for_space_highest_or && num_literal > num_or) continue;
			int max_literal_one_clause = min2(num_literal - num_or + 1, config.max_anded_literals);
			for (const vector<int>& num_literals_each_or : ways_to_split)
			{
				vector<int> num_clauses_each_literal_number(max_literal_one_clause + 1, 0);
				for (int n : num_literals_each_or) num_clauses_each_literal_number[n]++;
				vector<vector<vector<clause_t>>> clause_combs_lists;
				for (int num_literal_one_clause = 1; num_literal_one_clause <= max_literal_one_clause; num_literal_one_clause++)
				{
					int num_clauses_this_literal_number = num_clauses_each_literal_number[num_literal_one_clause];
					if (num_clauses_this_literal_number > 0)
					{
						clause_combs_lists.push_back(anded_clause_combs[num_literal_one_clause][num_clauses_this_literal_number]);
					}
				}
				vector<vector<vector<clause_t>>> clause_combs_lists_cart_product = cart_product(clause_combs_lists);
				inv_set_t invalidated_invs;
				// "bagging" groups anded clauses with the same literal count, e.g., [[3], [1,4], [2,5]] --> [[[3]], [[1,4], [2,5]]]
				for (const vector<vector<clause_t>>& bagged_candidate_inv : clause_combs_lists_cart_product)
				{
					// 1) check if bagged_candidate_inv is in the simplest form
					bool bagged_formula_is_simplified = check_if_bagged_formula_is_simplified(bagged_candidate_inv, number_predicates);
					if (!bagged_formula_is_simplified) continue;

					// 2) check if bagged_candidate_inv is a tautology
					inv_t candidate_inv;
					unbag_formula(bagged_candidate_inv, candidate_inv);
					if (tautology_DE_is_possible)
					{
						inv_t DE_mapped_candidate_inv;
						for (const clause_t& anded_clause : candidate_inv)
						{
							DE_mapped_candidate_inv.insert(DE_simplified_forms_dicts[anded_clause.size()][anded_clause]);
						}
						bool is_tautology_DE = helper.check_if_candidate_inv_is_tautology(DE_mapped_candidate_inv, number_predicates, checked_tautology_dict[number_predicates]);
						if (is_tautology_DE) continue;
					}
					
					// 3) check if candidate_inv is in extended_invs or invalidated_invs
					// if an and-superset of candidate_inv is in extended_invs, candidate_inv must be in extended_invs
					bool inv_already_in_extended_invs = extended_invs.find(candidate_inv) != extended_invs.end();
					if (inv_already_in_extended_invs) continue;
					bool inv_already_in_invalidated_invs = invalidated_invs.find(candidate_inv) != invalidated_invs.end();
					if (inv_already_in_invalidated_invs) continue;

					// 4) check if any or-subset of candidate_inv is in extended_invs
					bool subset_is_inv = false;
					if (num_or >= 2)
					{
						for (const clause_t& anded_clause : candidate_inv)
						{
							inv_t sub_candidate_inv = candidate_inv;
							sub_candidate_inv.erase(anded_clause);
							if (extended_invs.find(sub_candidate_inv) != extended_invs.end())
							{
								subset_is_inv = true;
								break;
							}
						}
					}
					if (subset_is_inv)
					{
						add_permuted_candidates(extended_invs, vars, is_unique_ordered, candidate_inv);
						if (exists_type_list.size() == 0) update_base_implied_formulas_each_clause_with_permutations(base_implied_formulas_each_clause, vars, is_unique_ordered, candidate_inv);
						continue;
					}

					// 5) check if candidate_inv is a forall_one_clause_and_exists_invariant (FOCAEI) redundant form
					bool is_FOCAEI_redundant = false;
					if (exists_type_list.size() > 0)
					{
						is_FOCAEI_redundant = helper.check_if_inv_is_FOCAEI_redundant(candidate_inv, extended_invs, deuniqued_extended_invs_dict.at(vars).at(forall_only_qalter)[exists_type_list[0]]);
					}
					if (is_FOCAEI_redundant)
					{
						add_inv_with_permutations_and_subsets(extended_invs, vars, is_unique_ordered, candidate_inv);
						continue;
					}

					// 6) check if any exists->forall predecessor of candidate_inv is in extended_invs
					bool predecessors_are_invs = false;
					bool is_first_exists_type = true;  // whether the current type is the first (according to type_order) existentially quantified type in qalter
					for (int type_index : exists_type_list)
					{
						qalter_t lower_qalter = qalter;
						lower_qalter[type_index] = false;
						if (is_first_exists_type)
						{
							// the current candidate_inv does not need to be enumerated, if it holds under the same vars and lower qalter (i.e., replace first exists with forall)
							// exists X1 X2. forall Y1 Y2. p(X1,X2,Y1,Y2) can be implied by either
							// forall X1 X2. forall Y1 Y2. p(X1,X2,Y1,Y2)
							const vector<map<vector<int>, vector<vector<int>>>>& lower_connected_components_dict = connected_components_dict_dict[vars][lower_qalter];
							const inv_set_t& deuniqued_invs = deuniqued_extended_invs_dict.at(vars).at(lower_qalter).at(type_index);
							bool deuniqued_form_is_inv = check_if_decomposable_candidate_in_extended(candidate_inv, lower_connected_components_dict, deuniqued_invs);
							if (deuniqued_form_is_inv)
							{
								predecessors_are_invs = true;
							}
						}
						else
						{
							const vector<map<clause_t, vector<clause_t>>>& lower_connected_components_dict = connected_components_dict_dict[vars][lower_qalter];
							const inv_set_t& lower_extended_invs = extended_invs_dict[vars][lower_qalter];
							bool candidate_in_extended = check_if_decomposable_candidate_in_extended(candidate_inv, lower_connected_components_dict, lower_extended_invs);
							if (candidate_in_extended)
							{
								predecessors_are_invs = true;
							}
						}
						if (predecessors_are_invs) break;
						is_first_exists_type = false;
					}
					if (predecessors_are_invs)
					{
						add_inv_with_permutations_and_subsets(extended_invs, vars, is_unique_ordered, candidate_inv);
						continue;
					}

					// 7) check candidate_inv against the samples
					bool inv_hold_on_samples = true;
					// for (map<inst_t, DataMatrix>::const_iterator it = inst_data_mat_dict.begin(); it != inst_data_mat_dict.end(); it++)  // for debug, use original csvs to check if data projection goes wrong
					for (map<inst_t, DataMatrix>::const_iterator it = inst_data_mat_dict_each_leading_forall.at(leading_forall_vars).begin(); it != inst_data_mat_dict_each_leading_forall.at(leading_forall_vars).end(); it++)
					{
						// candidate_inv must hold on every instance size
						// when is_unique_ordered does not exists in column_indices_dict.at(vars).at(inst), the candidate inv trivially holds
						// for example, if the instance has only one node, then forall N1 < N2. p(N1,N2) automatically holds on all samples
						const inst_t& inst = it->first;
						const DataMatrix& data_mat = it->second;
						if (column_indices_dict.at(vars).at(inst).find(is_unique_ordered) != column_indices_dict.at(vars).at(inst).end())
						{
							int check_result = check_if_inv_on_csv(vars, qalter, inst, candidate_inv, data_mat, column_indices_dict.at(vars).at(inst).at(is_unique_ordered));
							bool inv_hold_curr_inst = check_result == INV_HOLD_ON_CSV;
							if (!inv_hold_curr_inst)
							{
								inv_hold_on_samples = false;
								break;
							}
						}
					}
					if (inv_hold_on_samples)
					{
						inv_results.insert(candidate_inv);
						add_inv_with_permutations_and_subsets(extended_invs, vars, is_unique_ordered, candidate_inv);
						add_PQR_implied_invs(inv_results, extended_invs, vars, is_unique_ordered, base_implied_formulas_each_clause, anded_clauses, candidate_inv, exists_type_list.size() > 0);
						if (exists_type_list.size() == 0) update_base_implied_formulas_each_clause_with_permutations(base_implied_formulas_each_clause, vars, is_unique_ordered, candidate_inv);
					}
					else
					{
						add_permuted_candidates(invalidated_invs, vars, is_unique_ordered, candidate_inv);
					}
				}
			}
		}
	}
	if (config.one_to_one_exists) deuniqued_extended_invs_dict[vars][qalter];
	else calc_deuniqued_invs(vars, qalter, deuniqued_extended_invs_dict[vars][qalter]);
	// if (vars == vars_t({ 2 }) && qalter == qalter_t({ false })) exit(-1);  // for debug
	auto enumerate_dnf_end_time = time_now();
	cout << "enumerate_dnf time: " << std::fixed << std::setprecision(2) << double(time_diff(enumerate_dnf_end_time, enumerate_dnf_start_time))/1000000 << "s" << endl;
}

void Solver::remove_redundancy_in_anded_literal(const vars_t& vars, const vector<bool>& is_unique_ordered, const vector<vector<clause_t>>& anded_clauses_with_redundancy, vector<vector<clause_t>>& anded_clauses) const
{
	// for example, vars = [2,1,2], is_unique_ordered = [true,false,false], one anded clause is p(Y1,Z1) /\ q(X1,Z2)
	// from lower subtemplate we have invariant forall X1 < X2. forall Y1. forall Z1 Z2. ~p(Y1,Z1) \/ q(X1,Z2) (we call this "deuniqued" invariant, because it is effectively the conjunction of 2 or 3 invariants, depending on whether type Z has a total order)
	// then p(Y1,Z1) /\ q(X1,Z2) is redundant, thus does not need consideration
	assert(anded_clauses.size() == 0);
	int first_non_unique_type = num_types;
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		if (!is_unique_ordered[type_index])
		{
			first_non_unique_type = type_index;
			break;
		}
	}
	assert(first_non_unique_type != num_types);
	int number_predicates = predicates_dict.at(vars).size();
	for (const vector<clause_t>& anded_clauses_with_redundancy_one_literal_number : anded_clauses_with_redundancy)
	{
		vector<clause_t> non_redundant_anded_clauses_this_literal_number;
		if (anded_clauses_with_redundancy_one_literal_number.size() == 0)
		{
			anded_clauses.push_back(vector<clause_t>());
			continue;
		}
		int num_terms = anded_clauses_with_redundancy_one_literal_number[0].size();
		if (num_terms == 1)
		{
			anded_clauses.push_back(anded_clauses_with_redundancy_one_literal_number);  // with only one term p, no redundancy exists
			continue;
		}
		assert(num_terms >= 2);
		const inv_set_t& deuniqued_invs = deuniqued_extended_invs_dict.at(vars).at(forall_only_qalter)[first_non_unique_type];
		for (const clause_t& clause_to_check : anded_clauses_with_redundancy_one_literal_number)
		{
			// let's say the clause to check is p /\ ~q /\ r, if one of the following three holds, we should skip it
			// (1) p /\ ~q -> r   (2) p /\ r -> ~q    (3) ~q /\ r -> p, or put it in disjunctive form
			// (a) ~p \/ q \/ r   (b) ~p \/ ~q \/ ~r  (c) p \/ q \/ ~r
			// compared with the original clause, all but one literals are flipped
			bool clause_is_redundant = false;
			for (int p_not_to_flip = 0; p_not_to_flip < num_terms; p_not_to_flip++)
			{
				inv_t new_clause_as_inv;
				for (int i = 0; i < num_terms; i++)
				{
					if (i == p_not_to_flip) new_clause_as_inv.insert({ clause_to_check[i] });
					else new_clause_as_inv.insert({ neg_p(clause_to_check[i], number_predicates) });
				}
				if (deuniqued_invs.find(new_clause_as_inv) != deuniqued_invs.end())  // one of (a)(b)(c) is an invariant
				{
					clause_is_redundant = true;
					break;
				}
			}
			if (!clause_is_redundant)
			{
				non_redundant_anded_clauses_this_literal_number.push_back(clause_to_check);
			}
		}
		anded_clauses.push_back(non_redundant_anded_clauses_this_literal_number);
	}
	assert(anded_clauses.size() == anded_clauses_with_redundancy.size());
}

bool Solver::check_if_bagged_formula_is_simplified(const vector<vector<clause_t>>& bagged_formula, int number_predicates)
{
	unordered_map<vector<vector<vector<int>>>, bool, Vector3dHash>& curr_bagged_formula_simplified_dict = bagged_formula_simplified_dict[number_predicates];
	if (curr_bagged_formula_simplified_dict.find(bagged_formula) != curr_bagged_formula_simplified_dict.end())
		return(curr_bagged_formula_simplified_dict[bagged_formula]);
	int num_groups = bagged_formula.size();

	// first check if each anded_clause is the subset of any higher group anded_clause
	for (int group_index = 0; group_index < num_groups - 1; group_index++)
	{
		const vector<clause_t>& same_literal_count_group = bagged_formula[group_index];
		for (const clause_t& anded_clause : same_literal_count_group)
		{
			for (int higher_group_index = group_index + 1; higher_group_index < num_groups; higher_group_index++)
			{
				const vector<clause_t>& higher_group = bagged_formula[higher_group_index];
				int index_of_superset_clause = helper.check_if_clause_is_subset_of_any_clause_in_group(anded_clause, higher_group);
				if (index_of_superset_clause >= 0)  // -1 means superset does not exist
				{
					curr_bagged_formula_simplified_dict[bagged_formula] = false;
					return false;
				}
			}
		}
	}

	// second check if each anded_clause can be used to shorten other clauses
	clause_t dumb_clause; vector<clause_t> dumb_vector_clause;
	for (int group_index = 0; group_index < num_groups; group_index++)
	{
		const vector<clause_t>& same_literal_count_group = bagged_formula[group_index];
		for (const clause_t& anded_clause : same_literal_count_group)
		{
			for (int higher_group_index = 0; higher_group_index < num_groups; higher_group_index++)
			{
				const vector<clause_t>& higher_group = bagged_formula[higher_group_index];
				bool can_reduce = helper.check_if_clause_can_reduce_clauses_in_group(anded_clause, higher_group, number_predicates, dumb_clause, dumb_vector_clause);
				if (can_reduce)
				{
					curr_bagged_formula_simplified_dict[bagged_formula] = false;
					return false;
				}
			}
		}
	}

	// third check if after grouping predicates with the same literal(s), if any clause can shorten other clauses
	map<int, vector<vector<clause_t>>> sub_bagged_formula_each_literal;
	map<pair<int,int>, vector<vector<clause_t>>> sub_bagged_formula_each_literal_pair;
	for (int group_index = 0; group_index < num_groups; group_index++)
	{
		const vector<clause_t>& same_literal_count_group = bagged_formula[group_index];
		for (const clause_t& anded_clause : same_literal_count_group)
		{
			int anded_clause_length = anded_clause.size();
			if (anded_clause_length >= 2)  // single-literal clause will become none after literal grouping, does not need consideration
			{	
				for (int i = 0; i < anded_clause_length; i++)
				{
					clause_t new_clause = anded_clause;
					new_clause.erase(new_clause.begin() + i);
					sub_bagged_formula_each_literal[anded_clause[i]].resize(config.max_anded_literals);
					sub_bagged_formula_each_literal[anded_clause[i]][anded_clause_length - 1].push_back(new_clause);
				}
			}
			if (anded_clause_length >= 3)  // double-literal clause will become none after literal-pair grouping, does not need consideration
			{
				for (int i = 0; i < anded_clause_length; i++)
				{
					for (int j = i + 1; j < anded_clause_length; j++)
					{
						clause_t new_clause = anded_clause;
						new_clause.erase(new_clause.begin() + i);
						new_clause.erase(new_clause.begin() + j - 1);
						sub_bagged_formula_each_literal_pair[std::make_pair(anded_clause[i], anded_clause[j])].resize(config.max_anded_literals - 1);
						sub_bagged_formula_each_literal_pair[std::make_pair(anded_clause[i], anded_clause[j])][anded_clause_length - 2].push_back(new_clause);
					}
				}
			}
		}
	}
	for (map<int, vector<vector<clause_t>>>::const_iterator it = sub_bagged_formula_each_literal.begin(); it != sub_bagged_formula_each_literal.end(); it++)
	{
		const vector<vector<clause_t>>& clauses_each_literal_number = it->second;
		for (int reducer_literal_number = 1; reducer_literal_number <= config.max_anded_literals - 1; reducer_literal_number++)
		{
			const vector<clause_t>& reducer_clauses = clauses_each_literal_number[reducer_literal_number];
			for (const clause_t& reducer_clause : reducer_clauses)
			{
				for (int reducee_literal_number = 1; reducee_literal_number <= config.max_anded_literals - 1; reducee_literal_number++) 
				{
					const vector<clause_t>& reducee_clauses = clauses_each_literal_number[reducee_literal_number];
					if (reducee_clauses.size() > 0)
					{
						bool can_reduce = helper.check_if_clause_can_reduce_clauses_in_group(reducer_clause, reducee_clauses, number_predicates, dumb_clause, dumb_vector_clause);
						if (can_reduce)
						{
							curr_bagged_formula_simplified_dict[bagged_formula] = false;
							return false;
						}
					}
				}
			}
		}
	}
	for (map<pair<int, int>, vector<vector<clause_t>>>::const_iterator it = sub_bagged_formula_each_literal_pair.begin(); it != sub_bagged_formula_each_literal_pair.end(); it++)
	{
		const vector<vector<clause_t>>& clauses_each_literal_number = it->second;
		for (int reducer_literal_number = 1; reducer_literal_number <= config.max_anded_literals - 2; reducer_literal_number++)
		{
			const vector<clause_t>& reducer_clauses = clauses_each_literal_number[reducer_literal_number];
			for (const clause_t& reducer_clause : reducer_clauses)
			{
				for (int reducee_literal_number = 1; reducee_literal_number <= config.max_anded_literals - 2; reducee_literal_number++)
				{
					const vector<clause_t>& reducee_clauses = clauses_each_literal_number[reducee_literal_number];
					if (reducee_clauses.size() > 0)
					{
						bool can_reduce = helper.check_if_clause_can_reduce_clauses_in_group(reducer_clause, reducee_clauses, number_predicates, dumb_clause, dumb_vector_clause);
						if (can_reduce)
						{
							curr_bagged_formula_simplified_dict[bagged_formula] = false;
							return false;
						}
					}
				}
			}
		}
	}
	curr_bagged_formula_simplified_dict[bagged_formula] = true;
	return true;
}


bool Solver::check_if_inv(const DataMatrix& data_mat, const inv_t& comb) const
{
	/*
	int nrow = data_mat.nrow;
	int** data_ptr = data_mat.data_ptr;
	for (int row = 0; row < nrow; row++)
	{
		bool this_row_is_satisfied = false;
		for (int col : comb)
		{
			if (data_ptr[row][col] != 0)
			{
				this_row_is_satisfied = true;
				break;
			}
		}
		if (!this_row_is_satisfied) return false;
	}
	return true;
	*/
	return true;
}

int Solver::check_if_inv_on_csv(const vars_t& vars, const qalter_t& qalter, const inst_t& inst, const inv_t& candidate_inv, const DataMatrix& data_mat, const map<vector<int>, vector<int>>& one_column_indices_dict) const
{
	// example
	// vars: [2,2,1], qalter: [false, true, false], candidate_inv: [[0,3], [2]], data_mat has instance size [3,2,2]
	// then the candidate invariant has shape forall X1 < X2. exists Y1 Y2. forall Z1. ...
	// the keys one_column_indices_dict are [0,0,0], [0,0,1], [0,1,0], [0,1,1], ..., [0,3,0], [0,3,1], [1,0,0], ..., [1,3,1], [2,0,0], ..., [2,3,1]
	// the first element can take 3 values which corresponds to X1 X2 -> x1 x2 | x1 x3 | x2 x3, second element 4 values Y1 Y2 -> y1 y1 | y1 y2 | y2 y1 | y2 y2, third element 2 values Z1 -> z1 | z2
	int nrow = data_mat.nrow;
	int** data_ptr = data_mat.data_ptr;
	vector<int> num_mapping_each_type(num_types);
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	for (int i = 0; i < num_types; i++) num_mapping_each_type[i] = single_type_mappings[i][vars[i]][inst[i]].at(is_unique_ordered[i]).size();
	for (int row = 0; row < nrow; row++)
	{
		bool this_row_is_satisfied = true;
		const int* data_line = data_ptr[row];
		vector<int> counters(num_types, 0);
		while (true)
		{
			const vector<int>& curr_mapping = one_column_indices_dict.at(counters);
			vector<vector<int>> candidate_inv_as_data_indices;
			bool invalid_mapping_discovered = false;
			for (const clause_t& anded_clause : candidate_inv)
			{
				int anded_clause_length = anded_clause.size();
				clause_t mapped_clause(anded_clause);
				for (int i = 0; i < anded_clause_length; i++)
				{
					mapped_clause[i] = curr_mapping[anded_clause[i]];
					if (mapped_clause[i] < 0) invalid_mapping_discovered = true;
				}
				candidate_inv_as_data_indices.push_back(mapped_clause);
			}
			bool true_on_curr_counters = invalid_mapping_discovered ? true : check_if_qfree_dnf_formula_holds_on_data_line(data_line, candidate_inv_as_data_indices);
			bool true_on_current_level = true_on_curr_counters;
			bool current_level_unknown = false;
			// forall N1. p(N1) has two levels: the base level is whether p(n1), p(n2),... holds; the top level is whether forall N1. p(N1) holds
			// in general, a formula has num_types + 1 levels. At each level, some quantifier prefix are instantiated. Base level -> all instantiated; top level -> none instantiated.
			for (int type_index = num_types - 1; type_index >= 0; type_index--)
			{
				current_level_unknown = false;
				if (qalter[type_index])
				{
					if (true_on_current_level)
					{
						true_on_current_level = true;
					}
					else
					{
						if (counters[type_index] == num_mapping_each_type[type_index] - 1)
						{
							true_on_current_level = false;
						}
						else
						{
							current_level_unknown = true;
						}
					}
				}
				else
				{
					if (true_on_current_level)
					{
						if (counters[type_index] == num_mapping_each_type[type_index] - 1)
						{
							true_on_current_level = true;
						}
						else
						{
							current_level_unknown = true;
						}
					}
					else
					{
						true_on_current_level = false;
					}
				}
				if (current_level_unknown)
				{
					counters[type_index]++;
					for (int trailing_type_index = type_index + 1; trailing_type_index < num_types; trailing_type_index++) counters[trailing_type_index] = 0;
					break;
				}
			}
			if (!current_level_unknown)
			{
				// the loop above terminates by exhausting types rather than "break", we know the whether this data line satisfies the candidate inv
				this_row_is_satisfied = true_on_current_level;
				break;
			}
		}
		if (!this_row_is_satisfied)
		{
			return row;
		}
	}
	return INV_HOLD_ON_CSV;
}

bool Solver::check_if_qfree_dnf_formula_holds_on_data_line(const int* data_line, const vector<vector<int>>& candidate_inv_as_data_indices) const
{
	for (const vector<int>& anded_clause : candidate_inv_as_data_indices) 
	{
		bool this_clause_is_satisfied = true;
		for (int col : anded_clause)
		{
			if (data_line[col] == 0)
			{
				this_clause_is_satisfied = false;
				break;
			}
		}
		if (this_clause_is_satisfied) return true;
	}
	return false;
}

bool Solver::check_if_decomposable_candidate_in_extended(const inv_t& candidate_inv, const vector<map<clause_t, vector<clause_t>>>& connected_components_dict, const inv_set_t& extended_invs) const
{
	vector<vector<clause_t>> connected_components_each_clause;
	for (const clause_t& anded_clause : candidate_inv)
	{
		int anded_clause_length = anded_clause.size();
		map<clause_t, vector<clause_t>>::const_iterator it = connected_components_dict[anded_clause_length].find(anded_clause);
		if (it == connected_components_dict[anded_clause_length].end())
		{
			// this clause is still connected (i.e., allowed in the exists->forall predecessor)
			connected_components_each_clause.push_back({ anded_clause });
		}
		else
		{
			const vector<clause_t>& connected_components = it->second;
			connected_components_each_clause.push_back(connected_components);
		}
	}
	vector<vector<clause_t>> non_decomposable_candidate_invs = cart_product(connected_components_each_clause);
	for (const vector<clause_t>& non_decomposable_candidate_inv_vec : non_decomposable_candidate_invs)
	{
		inv_t non_decomposable_candidate_inv(non_decomposable_candidate_inv_vec.begin(), non_decomposable_candidate_inv_vec.end());
		if (extended_invs.find(non_decomposable_candidate_inv) == extended_invs.end())
		{
			// if any decomposed candidate inv is not in extended_inv, then the full decomposable candidate inv should be considered not in extended inv
			return false;
		}
	}
	return true;
}

void Solver::precompute_vars_self_mapping(const vars_t& vars, const qalter_t& qalter)
{
	const map<string, int>& p_to_idx = p_to_idx_dict[vars];
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	bool self_mapped_predicates_dict_already_calculated = self_mapped_predicates_dict[vars][is_unique_ordered].size() > 0; // calculated by another qalter with the same is_unique_ordered
	if (self_mapped_predicates_dict_already_calculated) return;
	const vector<string>& predicates = predicates_dict[vars];
	int num_predicates = predicates.size();
	int double_num_predicates = 2 * num_predicates;
	
	// calculate self_mapped_predicates_dict[vars][is_unique_ordered], which is used to calculate permuted invariants
	vector<vector<map<string, string>>> vars_mappings_each_type(num_types);
	for (int i = 0; i < num_types; i++)
	{
		if (is_unique_ordered[i] && (config.total_ordered_types.find(i) != config.total_ordered_types.end()))  // leading ordered forall variables cannot be permuted
		{
			vars_mappings_each_type[i] = { map<string,string>() };
			continue;
		}
		vector<vector<int>> this_type_mappings = single_type_self_mappings.at(i).at(vars[i]).at(vars[i]);
		// filter out N1 N2 -> N1 N1. This is not allowed in invariant permutation. exists X Y. p(X,Y) is not equivalent to exists X Y. p(X,X)
		vars_mappings_each_type[i].reserve(this_type_mappings.size());
		vector<string> input_var_list;
		construct_vars_vector(config.type_abbrs[config.type_order[i]], vars[i], input_var_list);
		for (const vector<int>& this_map_as_indices : this_type_mappings)
		{
			map<string, string> this_map;
			vector<string> projected_var_list;
			construct_vars_vector(config.type_abbrs[config.type_order[i]], this_map_as_indices, projected_var_list);
			for (int j = 0; j < vars[i]; j++) this_map[input_var_list[j]] = projected_var_list[j];
			vars_mappings_each_type[i].push_back(this_map);
		}
		if (config.one_to_one_exists && config.one_to_one.out_type == i)
		{
			vector<map<string, string>> bijection_mappings;
			helper.zip_merge_vector_of_map_string(vars_mappings_each_type[i - 1], vars_mappings_each_type[i], bijection_mappings);
			vars_mappings_each_type[i - 1] = { map<string,string>() };
			vars_mappings_each_type[i] = bijection_mappings;
		}
	}

	vector<vector<map<string, string>>> vars_mappings;
	vars_mappings = cart_product(vars_mappings_each_type);
	for (const vector<map<string, string>>& vars_map_list : vars_mappings)
	{
		// an example vars_map_list: [{"N1": "N2", "N2": "N1"}, {"T1":"T1"}]
		map<string, string> vars_map;
		join_vector_of_maps(vars_map_list, vars_map);
		vector<string> new_predicates;
		processor.remap_predicates(predicates, vars_map, new_predicates);
		vector<int> new_predicates_as_indices_of_predicates(double_num_predicates);
		for (int i = 0; i < num_predicates; i++)
		{
			if (p_to_idx.find(new_predicates[i]) == p_to_idx.end())
			{
				assert(column_compression_on || py_column_compression_detected);
				new_predicates_as_indices_of_predicates[i] = INVALID_PREDICATE_COLUMN;
			}
			else
			{
				new_predicates_as_indices_of_predicates[i] = p_to_idx.at(new_predicates[i]);
			}
		}
		for (int i = num_predicates; i < double_num_predicates; i++) new_predicates_as_indices_of_predicates[i] = new_predicates_as_indices_of_predicates[i - num_predicates] + num_predicates;
		self_mapped_predicates_dict[vars][is_unique_ordered].push_back(new_predicates_as_indices_of_predicates);
	}
}

void Solver::calc_self_mapped_predicates_each_mapping()
{
	for (const vars_t& vars : vars_traversal_order)
	{
		// calculate self_mapped_new_predicates_each_mapping[vars][(start_type, end_type)], which is used to calculate exists->forall predecessors
		// should only be used for the first existential type in qalter
		// later existential types, when converted to forall, does not need to distinguish N1 < N2 and N2 < N1 for itself and following forall types
		const vector<string>& predicates = predicates_dict.at(vars);
		int number_predicates = predicates.size();
		int double_number_predicates = 2 * number_predicates;
		const map<string, int>& p_to_idx = p_to_idx_dict.at(vars);
		for (int start_type = 0; start_type < num_types; start_type++)
		{
			for (int end_type = start_type + 1; end_type <= num_types; end_type++)
			{
				// if qalter = [false, true, false, true], first_exists = 1, second_exists = 3
				// if qalter = [false, false, false, false], first_exists = -1, second_exists = 4
				vector<vector<vector<int>>> indices_mappings_each_type(end_type - start_type);
				vector<vector<string>> input_vars_lists(end_type - start_type);
				for (int type_index = start_type; type_index < end_type; type_index++)
				{
					int num_vars_this_type = vars[type_index];
					construct_vars_vector(config.type_abbrs[config.type_order[type_index]], num_vars_this_type, input_vars_lists[type_index - start_type]);
					vector<vector<int>> mappings_this_type;
					for (int out_var_num = 1; out_var_num <= num_vars_this_type; out_var_num++)
					{
						const vector<vector<int>>& mappings_this_type_out_var = single_type_self_mappings[type_index][num_vars_this_type][out_var_num];
						mappings_this_type.insert(mappings_this_type.end(), mappings_this_type_out_var.begin(), mappings_this_type_out_var.end());
					}
					indices_mappings_each_type[type_index - start_type] = mappings_this_type;
				}
				vector<vector<vector<int>>> indices_mappings_across_types = cart_product(indices_mappings_each_type);
				for (const vector<vector<int>>& indices_mapping_across_types : indices_mappings_across_types)
				{
					map<string, string> vars_map;
					for (int type_index = start_type; type_index < end_type; type_index++)
					{
						vector<string> projected_var_list;
						construct_vars_vector(config.type_abbrs[config.type_order[type_index]], indices_mapping_across_types[type_index - start_type], projected_var_list);
						for (int j = 0; j < vars[type_index]; j++) vars_map[input_vars_lists[type_index - start_type][j]] = projected_var_list[j];
					}
					vector<string> new_predicates;
					processor.remap_predicates(predicates, vars_map, new_predicates);
					vector<int> new_predicates_as_indices_of_predicates(double_number_predicates);
					for (int i = 0; i < number_predicates; i++)
					{
						if (p_to_idx.find(new_predicates[i]) == p_to_idx.end())
						{
							assert(column_compression_on || py_column_compression_detected);
							new_predicates_as_indices_of_predicates[i] = INVALID_PREDICATE_COLUMN;
						}
						else
						{
							new_predicates_as_indices_of_predicates[i] = p_to_idx.at(new_predicates[i]);
						}
					}
					for (int i = number_predicates; i < double_number_predicates; i++) new_predicates_as_indices_of_predicates[i] = new_predicates_as_indices_of_predicates[i - number_predicates] + number_predicates;
					self_mapped_new_predicates_each_mapping[vars][std::make_pair(start_type,end_type)][indices_mapping_across_types] = new_predicates_as_indices_of_predicates;
				}
			}
		}
	}
}

void Solver::add_inv_with_permutations_and_subsets(inv_set_t& extended_invs, const vars_t& vars, const vector<bool>& is_unique_ordered, const inv_t& candidate_inv)
{
	int number_predicates = predicates_dict[vars].size();
	int number_clauses = candidate_inv.size();
	vector<vector<clause_t>> power_set_each_clause;
	power_set_each_clause.reserve(number_clauses);
	for (const clause_t& anded_clause : candidate_inv)
	{
		vector<clause_t> anded_clause_subsets;
		calc_powerset(anded_clause, anded_clause_subsets);
		power_set_each_clause.push_back(anded_clause_subsets);
	}
	vector<vector<clause_t>> all_sub_candidate_invs = cart_product(power_set_each_clause);
	for (const vector<clause_t>& sub_candidate_inv : all_sub_candidate_invs)
	{
		vector<vector<clause_t>> anded_clause_each_term_number(config.max_anded_literals + 1);
		for (const clause_t& anded_clause : sub_candidate_inv)
		{
			anded_clause_each_term_number[anded_clause.size()].push_back(anded_clause);
		}
		vector<vector<clause_t>> new_bagged_candidate_inv;
		for (int num_terms = 1; num_terms <= config.max_anded_literals; num_terms++)
		{
			if (anded_clause_each_term_number[num_terms].size() > 0)
			{
				std::sort(anded_clause_each_term_number[num_terms].begin(), anded_clause_each_term_number[num_terms].end());
				new_bagged_candidate_inv.push_back(anded_clause_each_term_number[num_terms]);
			}
		}
		bool formula_is_simplified = check_if_bagged_formula_is_simplified(new_bagged_candidate_inv, number_predicates);
		if (formula_is_simplified)
		{
			inv_t new_candidate_inv;
			unbag_formula(new_bagged_candidate_inv, new_candidate_inv);
			add_permuted_candidates(extended_invs, vars, is_unique_ordered, new_candidate_inv);
		}
	}
}

void Solver::add_PQR_implied_invs(inv_set_t& inv_results, inv_set_t& extended_invs, const vars_t& vars, const vector<bool>& is_unique_ordered, const unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause, const vector<vector<clause_t>>& considered_anded_clauses, const inv_t& candidate_inv, bool remove_inv_if_implied) const
{
	// base_extended_invs must be at forall_only_qalter, the implementation should be aware that extended_invs and base_extended_invs can be the same object
	inv_set_t implied_invs;
	vector<unordered_set<clause_t, VectorHash>> considered_anded_clauses_sets;
	for (const vector<clause_t>& anded_clauses_one_literal : considered_anded_clauses)
	{
		considered_anded_clauses_sets.push_back(unordered_set<clause_t, VectorHash>(anded_clauses_one_literal.begin(), anded_clauses_one_literal.end()));
	}

	vector<vector<inv_t>> implied_formulas_each_clause;
	for (const clause_t& anded_clause : candidate_inv)  // list what formulas each anded clause can imply
	{
		unordered_set<vector<int>, VectorHash> implied_ored_clauses;
		helper.integrate_implied_ored_clauses(base_implied_formulas_each_clause, anded_clause, implied_ored_clauses);
		vector<int> implied_single_literals;
		for (int literal_ : anded_clause) implied_single_literals.push_back(literal_);  // p /\ q -> p
		vector<inv_t> implied_formulas;  // formulas implied by anded_clause, an implied formula can have at most (config.max_ored_clauses - 1) clauses
		// 1. implied formulas with at least two clauses
		for (const vector<int>& implied_ored_clause : implied_ored_clauses)
		{
			if (implied_ored_clause.size() == 1)
			{
				implied_single_literals.push_back(implied_ored_clause[0]);
			}
			else
			{
				inv_t implied_ored_clause_as_inv;
				if (anded_clause.size() + implied_ored_clause.size() >= 3) continue;  // temporary solution
				for (int literal_ : implied_ored_clause) implied_ored_clause_as_inv.insert({ literal_ });
				implied_formulas.push_back(implied_ored_clause_as_inv);
			}
		}

		// 2. implied formulas with a single clause
		std::sort(implied_single_literals.begin(), implied_single_literals.end());
		for (int num_terms = 1; num_terms <= config.max_anded_literals; num_terms++)
		{
			const unordered_set<clause_t, VectorHash>& curr_anded_clauses_set = considered_anded_clauses_sets[num_terms];
			vector<clause_t> implied_anded_clauses;
			calc_combinations(implied_single_literals, num_terms, implied_anded_clauses);
			for (const clause_t& implied_anded_clause : implied_anded_clauses)
			{
				if (curr_anded_clauses_set.find(implied_anded_clause) != curr_anded_clauses_set.end()) // we should only include "considered" anded clauses
				{
					implied_formulas.push_back({ implied_anded_clause });
				}
			}
		}
		implied_formulas_each_clause.push_back(implied_formulas);
	}

	vector<vector<inv_t>> implied_formulas_cart_product = cart_product(implied_formulas_each_clause);
	for (const vector<inv_t>& implied_formula_across_clauses : implied_formulas_cart_product)
	{
		inv_t merged_inv;
		merge_inv(implied_formula_across_clauses, merged_inv);
		// we know merged_inv can be implied by candidate_inv
		if (helper.check_if_inv_within_max_or_and_literal(merged_inv))
		{
			const vector<vector<int>>& all_new_predicates_indices = self_mapped_predicates_dict.at(vars).at(is_unique_ordered);
			for (const vector<int>& new_predicates_indices : all_new_predicates_indices)
			{
				inv_t mapped_merged_inv;
				bool mapping_valid = map_inv_with_column_indices(merged_inv, new_predicates_indices, mapped_merged_inv);
				if (!mapping_valid) continue;
				extended_invs.insert(mapped_merged_inv);
				if (remove_inv_if_implied)  // we only remove new_candidate_inv if the current qalter has existential quantifiers
				{
					if (mapped_merged_inv != candidate_inv)  // we do not remove candidate_inv itself from inv_results
					{
						inv_results.erase(mapped_merged_inv);
					}
				}
			}
		}
	}
}

void Solver::add_permuted_candidates(inv_set_t& formula_set, const vars_t& vars, const vector<bool>& is_unique_ordered, const inv_t& candidate_inv)
{
	const vector<vector<int>>& all_new_predicates_indices = self_mapped_predicates_dict[vars][is_unique_ordered];
	for (const vector<int>& new_predicates_indices : all_new_predicates_indices)
	{
		inv_t new_candidate_inv;
		bool mapping_valid = map_inv_with_column_indices(candidate_inv, new_predicates_indices, new_candidate_inv);
		if (mapping_valid) formula_set.insert(new_candidate_inv);
	}
}

void Solver::update_base_implied_formulas_each_clause_with_permutations(unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause, const vars_t& vars, const vector<bool>& is_unique_ordered, const inv_t& candidate_inv) const
{
	// we find a new invariant forall X1 != X2. p(X1,X2) \/ ~q(X1) \/ r(X2), either from checking against csv files or realizing one of its subsets is an invariant
	// this function will add implications ~p(X1,X2) /\ q(X1) -> r(X2), ..., ~r(X1) -> p(X2,X1) \/ ~q(X2) to base_implied_formulas_each_clause
	const vector<vector<int>>& all_new_predicates_indices = self_mapped_predicates_dict.at(vars).at(is_unique_ordered);
	int number_predicates = predicates_dict.at(vars).size();
	for (const vector<int>& new_predicates_indices : all_new_predicates_indices)
	{
		inv_t new_candidate_inv;
		bool mapping_valid = map_inv_with_column_indices(candidate_inv, new_predicates_indices, new_candidate_inv);
		if (mapping_valid) helper.update_base_implied_formulas_each_clause(new_candidate_inv, number_predicates, base_implied_formulas_each_clause);
	}
}

void Solver::generalize_exists_xpxx_invs(const vars_t& low_vars, const vars_t& high_vars, const qalter_t& qalter, const inv_set_t& extended_invs, inv_set_t& succ_extended_invs) const
{
	// only handles exists X1. p(X1) \/ q(X1) => exists X1 X2. p(X1) \/ q(X2)
	// does not support exists X1. p(X1,X1) -> exists X1 X2. p(X1,X2)
	// does not support exists X1 X2. p(X1) \/ q(X2) \/ r(X2) => exists X1 X2 X3. p(X1) \/ q(X2) \/ r(X3)
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		if (high_vars[type_index] == low_vars[type_index] + 1)  // high_vars has one more variable of this type compared with low_vars
		{
			if (qalter[type_index])
			{
				cout << "type_index in generalize_exists_xpxx_invs core:" << type_index << endl;
				if (low_vars[type_index] >= 2)
				{
					cout << "Error in generalize_exists_xpxx_invs! Not implemented yet!" << endl;
					exit(-1);
				}
				assert(low_vars[type_index] == 1);
				const vector<string>& lower_predicates = predicates_dict.at(low_vars);
				const vector<string>& higher_predicates = predicates_dict.at(high_vars);
				int num_lower_predicates = lower_predicates.size();
				int num_higher_predicates = higher_predicates.size(); 
				string var_name = config.type_abbrs.at(config.type_order[type_index]) + "1";
				string var_name_2 = config.type_abbrs.at(config.type_order[type_index]) + "2";
				map<string, string> sole_var_map;
				sole_var_map[var_name] = var_name_2;
				vector<string> mapped_lower_predicates;
				processor.remap_predicates(lower_predicates, sole_var_map, mapped_lower_predicates);
				const vector<int> columns_as_vec = var_in_p_dict.at(low_vars).at(var_name);  // columns with X1, including negated predicates
				set<int> columns(columns_as_vec.begin(), columns_as_vec.end());
				vector<vector<int>> mapped_columns_each_p(2*num_lower_predicates);
				for (int i = 0; i < num_lower_predicates; i++)
				{
					int mapped_col = p_to_idx_dict.at(high_vars).at(lower_predicates[i]);
					vector<int> mapped_cols_this_p({ mapped_col });
					vector<int> mapped_cols_this_p_negated({ mapped_col + num_higher_predicates });
					if (columns.find(i) != columns.end())  // this predicate includes X1
					{
						int other_mapped_col = p_to_idx_dict.at(high_vars).at(mapped_lower_predicates[i]);
						mapped_cols_this_p.push_back(other_mapped_col);
						mapped_cols_this_p_negated.push_back(other_mapped_col + num_higher_predicates);
					}
					mapped_columns_each_p[i] = mapped_cols_this_p;
					mapped_columns_each_p[i + num_lower_predicates] = mapped_cols_this_p_negated;
				}
				
				for (const inv_t& inv : extended_invs)
				{
					vector<vector<clause_t>> mapped_clauses_each_clause;
					for (const clause_t& anded_clause : inv)
					{
						vector<vector<int>> mapped_columns_each_p_in_clause;
						for (int literal_ : anded_clause) mapped_columns_each_p_in_clause.push_back(mapped_columns_each_p[literal_]);
						vector<clause_t> mapped_clauses = cart_product(mapped_columns_each_p_in_clause);
						for (vector<int>& mapped_clause : mapped_clauses) std::sort(mapped_clause.begin(), mapped_clause.end());
						mapped_clauses_each_clause.push_back(mapped_clauses);
					}
					vector<vector<clause_t>> mapped_invs_as_vecvec = cart_product(mapped_clauses_each_clause);
					for (const vector<clause_t>& mapped_inv_as_vecvec : mapped_invs_as_vecvec)
					{
						inv_t mapped_inv(mapped_inv_as_vecvec.begin(), mapped_inv_as_vecvec.end());
						succ_extended_invs.insert(mapped_inv);
					}
				}
			}
		}
	}
}

void Solver::calc_deuniqued_invs(const vars_t& vars, const qalter_t& qalter, vector<inv_set_t>& deuniqued_invs)
{
	// for example, if vars=[1,2,1], qalter=[false,false,true]
	// the current template is forall X1. forall Y1 < Y2. exists Z1. ...
	// there are two elements in the output deuniqued_invs, the indices 0 and 1 represent the first deuniqued type, both corresponds to forall X1. forall Y1 Y2. exists Z1. ...
	// [true,true,false] gives the identical result as extended_invs_dict[vars][qalter] so we do not record it
	// one important property: deuniqued_invs[any-key] should be a subset of extended_invs_dict[vars][qalter]
	const inv_set_t& curr_extended_invs = extended_invs_dict.at(vars).at(qalter);
	int number_predicates = predicates_dict.at(vars).size();
	int double_number_predicates = 2 * number_predicates;

	int first_exists_type = num_types;
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		if (qalter[type_index])
		{
			first_exists_type = type_index;
			break;
		}
	}
	deuniqued_invs.resize(num_types);
	for (int first_deuniqued_type = 0; first_deuniqued_type < first_exists_type; first_deuniqued_type++)
	{
		vector<bool> is_unique_ordered(num_types, false);
		for (int i = 0; i < first_deuniqued_type; i++) is_unique_ordered[i] = true;
		vector<vector<vector<vector<int>>>> vars_mappings_each_forall_type;
		vector<int> var_num_each_forall_type;
		for (int forall_type_index = first_deuniqued_type; forall_type_index < num_types; forall_type_index++)
		{
			if (qalter[forall_type_index]) break;  // second existentially quantified type found
			int var_num_this_forall_type = vars[forall_type_index];
			vector<vector<vector<int>>> vars_mappings_this_type_each_out_num;
			for (int out_num = 1; out_num <= var_num_this_forall_type; out_num++)
			{
				const vector<vector<int>>& vars_mappings_this_type_and_out_num = single_type_self_mappings[forall_type_index][var_num_this_forall_type][out_num];
				vars_mappings_this_type_each_out_num.push_back(vars_mappings_this_type_and_out_num);
			}
			vars_mappings_each_forall_type.push_back(vars_mappings_this_type_each_out_num);
			var_num_each_forall_type.push_back(var_num_this_forall_type);
		}
		// to check if forall X1. forall Y1 Y2. forall Z1 Z2. p(X1,Y1,Y2,Z1,Z2) holds, we need to check multiple formulas at four different sub-vars
		// at vars [1,2,2].  forall X1. forall Y1 < Y2. forall Z1 < Z2. p(X1,Y1,Y2,Z1,Z2)
		//                   forall X1. forall Y1 < Y2. forall Z1 < Z2. p(X1,Y2,Y1,Z1,Z2)
		//                   forall X1. forall Y1 < Y2. forall Z1 < Z2. p(X1,Y1,Y2,Z2,Z1)
		//                   forall X1. forall Y1 < Y2. forall Z1 < Z2. p(X1,Y2,Y1,Z2,Z1)
		// at vars [1,1,2].  forall X1. forall Y1. forall Z1 < Z2. p(X1,Y1,Y1,Z1,Z2)
		//                   forall X1. forall Y1. forall Z1 < Z2. p(X1,Y1,Y1,Z2,Z1)
		// at vars [1,2,1].  forall X1. forall Y1 < Y2. forall Z1. p(X1,Y1,Y2,Z1,Z1)
		//                   forall X1. forall Y1 < Y2. forall Z1. p(X1,Y2,Y1,Z1,Z1)
		// at vars [1,1,1].  forall X1. forall Y1. forall Z1. p(X1,Y1,Y1,Z1,Z1)
		// the index number below uses modular operator to iterate over each sub-vars
		int index_number_total = 1;
		for (int var_num_this_forall_type : var_num_each_forall_type) index_number_total *= var_num_this_forall_type;
		int num_forall_types = var_num_each_forall_type.size();
		map<vector<int>, vector<vector<vector<int>>>> vars_mappings_each_forall_out_var_list;
		// key is the out number of forall types following the first exists->forall, in the example above, there are four possible keys, [2,2], [1,2], [2,1], [1,1]
		// value is the list of possible mappings, each mapping consists of mapping for each forall type
		// key [2,2] has value [[[1,2],[1,2]], [[1,2],[2,1]], [[2,1],[1,2]], [[2,1],[2,1]]]
		for (int index_number = 0; index_number < index_number_total; index_number++)
		{
			vector<int> curr_forall_type_out_vars(num_forall_types);
			int q = index_number;
			for (int i = num_forall_types - 1; i >= 0; i--)
			{
				curr_forall_type_out_vars[i] = q % var_num_each_forall_type[i] + 1;
				q = q / var_num_each_forall_type[i];
			}
			vector<vector<vector<int>>> vars_mappings_each_forall_type_current_out_vars(num_forall_types);
			for (int i = 0; i < num_forall_types; i++) vars_mappings_each_forall_type_current_out_vars[i] = vars_mappings_each_forall_type[i][curr_forall_type_out_vars[i] - 1];
			vector<vector<vector<int>>> vars_mappings_curr_forall_out_var_list = cart_product(vars_mappings_each_forall_type_current_out_vars);
			vars_mappings_each_forall_out_var_list[curr_forall_type_out_vars] = vars_mappings_curr_forall_out_var_list;
		}

		map<vars_t, vector<vector<int>>> column_indices_list_each_lower_vars;  // a list of predicates mappings, if candidate_inv holds on all these mappings at the lower qalter, we do not enumerate it
		for (map<vector<int>, vector<vector<vector<int>>>>::const_iterator it = vars_mappings_each_forall_out_var_list.begin(); it != vars_mappings_each_forall_out_var_list.end(); it++)
		{
			const vector<int>& curr_forall_type_out_vars = it->first;
			const vector<vector<vector<int>>>& curr_vars_mappings_list = it->second;
			// construct the current complete vars
			vars_t lower_vars = vars;
			for (int i = first_deuniqued_type; i < first_deuniqued_type + num_forall_types; i++) lower_vars[i] = curr_forall_type_out_vars[i - first_deuniqued_type];
			const vector<int>& highlowvars_predicates_mapping = highlowvars_column_indices_dict.at(vars).at(lower_vars);
			vector<vector<int>> complete_predicates_mappings;
			for (const vector<vector<int>>& curr_vars_mappings : curr_vars_mappings_list)
			{
				const vector<int>& predicates_mapping = self_mapped_new_predicates_each_mapping.at(vars).at(std::make_pair(first_deuniqued_type,first_exists_type)).at(curr_vars_mappings);
				vector<int> complete_predicates_mapping(double_number_predicates);
				for (int i = 0; i < double_number_predicates; i++)
				{
					if (predicates_mapping[i] < 0) complete_predicates_mapping[i] = INVALID_PREDICATE_COLUMN;
					else complete_predicates_mapping[i] = highlowvars_predicates_mapping.at(predicates_mapping[i]);
				}
				complete_predicates_mappings.push_back(complete_predicates_mapping);
			}
			column_indices_list_each_lower_vars[lower_vars] = complete_predicates_mappings;
		}
		
		inv_set_t invalidated_invs;
		for (const inv_t& inv : curr_extended_invs)
		{
			if (deuniqued_invs[first_deuniqued_type].find(inv) != deuniqued_invs[first_deuniqued_type].end()) continue;  // inv's equivalent form already validated
			if (invalidated_invs.find(inv) != invalidated_invs.end()) continue;                                    // inv's equivalent form already invalidated
			bool holds_on_all_lower_vars_forms = true;
			for (map<vars_t, vector<vector<int>>>::const_iterator it = column_indices_list_each_lower_vars.begin(); it != column_indices_list_each_lower_vars.end(); it++)
			{
				bool succeeds_on_this_subvars = true;
				const vars_t& lower_vars = it->first;
				const vector<vector<int>>& column_indices_list = it->second;
				int number_lower_predicates = predicates_dict.at(lower_vars).size();
				const inv_set_t& lower_extended_invs = extended_invs_dict[lower_vars][qalter];
				for (const vector<int>& column_indices : column_indices_list)
				{
					inv_t mapped_inv;
					bool mapping_valid = map_inv_with_column_indices(inv, column_indices, mapped_inv);
					if (!mapping_valid) continue;  // I have doubts about the old implementation here
					bool mapped_candidate_in_extended = lower_extended_invs.find(mapped_inv) != lower_extended_invs.end();
					if (!mapped_candidate_in_extended)
					{
						bool mapped_candidate_is_tautology = helper.check_if_candidate_inv_is_tautology(mapped_inv, number_lower_predicates, checked_tautology_dict[number_lower_predicates]);
						if (!mapped_candidate_is_tautology)
						{
							succeeds_on_this_subvars = false;
							break;
						}
					}
				}
				if (!succeeds_on_this_subvars)
				{
					holds_on_all_lower_vars_forms = false;
					break;
				}
			}
			if (holds_on_all_lower_vars_forms)
			{
				add_permuted_candidates(deuniqued_invs[first_deuniqued_type], vars, is_unique_ordered, inv);
			}
			else
			{
				add_permuted_candidates(invalidated_invs, vars, is_unique_ordered, inv);
			}
		}
	}
}

void Solver::find_strengthen_safety_invs()
{
	vars_t all_one_vars(num_types, 1);
	const vector<string>& predicates_at_lowest_vars = predicates_dict.at(all_one_vars);
	int num_predicates_lowest_vars = predicates_at_lowest_vars.size();
	const inv_set_t& min_vars_invs = invs_dict.at(all_one_vars).at(qalter_t(num_types, false));
	inv_set_t size_two_min_vars_invs;
	for (const inv_t& inv : min_vars_invs)
	{
		if (inv.size() == 2) size_two_min_vars_invs.insert(inv);
	}
	unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash> base_implied_formulas_each_clause;
	helper.calc_base_implied_formulas_each_clause(predicates_dict.at(vars_t(num_types, 1)).size(), size_two_min_vars_invs, base_implied_formulas_each_clause);

	for (const string& safety_property_str : config.safety_properties)
	{
		// transform safety property from string to (vars, qalter, inv) triple
		vars_t vars(num_types);
		qalter_t qalter(num_types);
		vector<tuple<string, vector<string>, bool>> inv_rep;
		bool safety_property_parsed = processor.parse_inv_str(safety_property_str, vars, qalter, inv_rep);
		if (!safety_property_parsed) continue;
		// find possible predicate weakening transforms to make
		set<tuple<string, string, bool, bool>> possible_transforms;
		for (const tuple<string, vector<string>, bool>& p_triple : inv_rep)
		{
			const string& relation_name = std::get<0>(p_triple);
			assert(config.relations.find(relation_name) != config.relations.end());
			const vector<int> relation_signature = config.relations.at(relation_name);
			if (relation_signature.size() == 1)
			{
				string query_predicate = relation_name + "(" + config.type_abbr_list[relation_signature[0]] + "1)";
				assert(std::find(predicates_at_lowest_vars.begin(), predicates_at_lowest_vars.end(), query_predicate) != predicates_at_lowest_vars.end());
				int query_predicate_index = std::find(predicates_at_lowest_vars.begin(), predicates_at_lowest_vars.end(), query_predicate) - predicates_at_lowest_vars.begin();
				if (std::get<2>(p_triple)) query_predicate_index += num_predicates_lowest_vars;
				// we want to find stronger forms of predicate query_predicate_index, but we only have base_implied_formulas_each_clause which records the weaker form of each predicate
				// so we check the weaker form of !query_predicate_index, if q is such a weaker form, then !q is a stronger form of query_predicate_index
				if (base_implied_formulas_each_clause.find({ neg_p(query_predicate_index, num_predicates_lowest_vars) }) != base_implied_formulas_each_clause.end())
				{
					const unordered_set<vector<int>, VectorHash>& weaker_literal_set = base_implied_formulas_each_clause.at({ neg_p(query_predicate_index, num_predicates_lowest_vars) });
					for (const vector<int>& weaker_literal : weaker_literal_set)
					{
						assert(weaker_literal.size() == 1);
						int stronger_literal = neg_p(weaker_literal[0], num_predicates_lowest_vars);
						string weaker_predicate = predicates_at_lowest_vars.at(stronger_literal % num_predicates_lowest_vars);
						bool weaker_predicate_is_negated = stronger_literal >= num_predicates_lowest_vars;
						vector<string> weaker_predicate_args;
						string weaker_relation_name = processor.parse_predicate_str(weaker_predicate, weaker_predicate_args);
						if (weaker_predicate_args.size() == 1)
						{
							possible_transforms.insert({ relation_name, weaker_relation_name, std::get<2>(p_triple), weaker_predicate_is_negated });
						}
					}
				}
			}
		}
		for (const tuple<string, string, bool, bool>& transform : possible_transforms)
		{
			string new_inv_str = processor.generate_new_inv_str(inv_rep, transform);
			solver_more_invs.push_back({ vars, qalter, new_inv_str });
		}
		cout << "more_invs from strenthening the safety property" << endl;
		for (const auto& more_inv_triple : solver_more_invs)
		{
			cout << vec_to_str(std::get<0>(more_inv_triple)) << "; " << vec_to_str(std::get<1>(more_inv_triple)) << "; " << std::get<2>(more_inv_triple) << endl;
		}
	}
}

void Solver::early_preparations()
{
	calc_predicates_dict();
	calc_varinp_and_ptoidx();
	calc_single_type_mappings();  // map quantified variables to instance objects
	calc_single_type_self_mappings();  // map quantified variables to quantified variables
	calc_column_indices_dict();
}

void Solver::auto_solve()
{
	auto early_prep_start_time = time_now();
	early_preparations();
	
	calc_vars_traversal_order();  // store a valid traversal order of the quantified variable set in vars_traversal_order
	calc_highlowvars_column_indices_dict();
	calc_lowhighvars_column_indices_dict();
	calc_inst_data_mat_dict_each_leading_forall();
	calc_vars_qalters_exists_number();
	precompute_vars_self_mapping_bulk();
	calc_self_mapped_predicates_each_mapping();
	split_n_into_k_numbers_bulk(config.max_literal, config.max_ored_clauses, config.max_anded_literals, n_into_k);
	auto late_prep_end_time = time_now();
	cout << "Solver preparation time: " << std::fixed << std::setprecision(2) << double(time_diff(late_prep_end_time, early_prep_start_time))/1000000 << "s" << endl;

	// first enumerate existential-quantifier-free invariants, then one exists, two exists, and so on
	for (int num_exists = 0; num_exists <= config.max_exists; num_exists++)
	{
		// iterate through each subtemplate and enumerate candidate invariants
		for (const vars_t& vars : vars_traversal_order)
		{
			for (const qalter_t& qalter : vars_qalter_exists_number[vars][num_exists])
			{
				vector<bool> is_unique_ordered; qalter_to_unique_ordered(qalter, is_unique_ordered);
				inv_set_t invs;
				cout << "enumerating vars " << vec_to_str(vars) << " and qalter " << vec_to_str(qalter) << endl;
				enumerate_dnf(vars, qalter, invs, extended_invs_dict[vars][qalter]);
				invs_dict[vars][qalter] = invs;
				// for each vars successor succesor of the current subtemplate, project the checked invariants

				auto inv_generalization_start_time = time_now();
				for (map<vars_t, map<vector<bool>, vector<vector<int>>>>::const_iterator it = lowhighvars_column_indices_dict[vars].begin(); it != lowhighvars_column_indices_dict[vars].end(); it++)
				{
					const vars_t& successor = it->first;
					int successor_num_exists = 0;
					for (int i = 0; i < num_types; i++) if (qalter[i]) successor_num_exists += successor[i];
					if (successor_num_exists > config.max_exists) continue;  // (successor, qalter) pair is out of the current template
					const vector<vector<int>>& column_indices_list = it->second.at(is_unique_ordered);
					inv_set_t new_extended_invs;
					helper.generalize_invs(extended_invs_dict[vars][qalter], column_indices_list, new_extended_invs);
					extended_invs_dict[successor][qalter].insert(new_extended_invs.begin(), new_extended_invs.end());
					new_extended_invs.clear();
					generalize_exists_xpxx_invs(vars, successor, qalter, extended_invs_dict.at(vars).at(qalter), new_extended_invs);  // TODO-now: fix
					extended_invs_dict[successor][qalter].insert(new_extended_invs.begin(), new_extended_invs.end());
				}
				auto inv_generalization_end_time = time_now();
				int inv_generalization_time = time_diff(inv_generalization_end_time, inv_generalization_start_time);
				cout << "inv generalization_time: " << std::fixed << std::setprecision(2) << double(inv_generalization_time)/1000000 << "s" << endl;
			}
		}
	}
	if (config.hard) find_strengthen_safety_invs();
	processor.add_checked_invs(solver_more_invs);
	
	cout << "Invariant enumeration finished" << endl;
}

void Solver::encode_and_output(const string& outfile, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	vector<string> str_invs;
	encoder.encode_invs_dict(invs_dict, predicates_dict, str_invs, id_to_inv, more_invs);
	encoder.append_invs_ivy(input_ivy_file, outfile, str_invs);
}

void Solver::run_simplifiable_unit_tests()
{
	vector<vector<clause_t>> formula0 = { {{0}} };                        // p
	cout << check_if_bagged_formula_is_simplified(formula0, 10) << endl;  // should be true
	vector<vector<clause_t>> formula1 = { {{0, 2}, {0, 12}} };            // (p /\ q) \/ (p /\ ~q)
	cout << check_if_bagged_formula_is_simplified(formula1, 10) << endl;  // should be false
	vector<vector<clause_t>> formula2 = { {{0, 2}}, {{0, 12, 13} }};      // (p /\ q) \/ (p /\ ~q /\ ~r)
	cout << check_if_bagged_formula_is_simplified(formula2, 10) << endl;  // should be false
	vector<vector<clause_t>> formula3 = { {{0, 3, 12}, {0, 12, 13}} };    // (p /\ r /\ ~q) \/ (p /\ ~q /\ ~r)
	cout << check_if_bagged_formula_is_simplified(formula3, 10) << endl;  // should be false
	vector<vector<clause_t>> formula4 = { {{5}}, {{4, 10, 11}, {0, 2, 4}, {1, 2, 4}} };  // (~p /\ ~q /\ s) \/ (p /\ r /\ s) \/ (q /\ r /\ s) \/ t
	cout << check_if_bagged_formula_is_simplified(formula4, 10) << endl;  // should be false
	vector<vector<clause_t>> formula5 = { {{0, 2}, {10, 12}} };           // (p /\ q) \/ (~p /\ ~q)
	cout << check_if_bagged_formula_is_simplified(formula5, 10) << endl;  // should be true
	vector<vector<clause_t>> formula6 = { {{0, 12}}, {{0, 3, 12} } };     // (p /\ ~q) \/ (p /\ r /\ ~q)
	cout << check_if_bagged_formula_is_simplified(formula6, 10) << endl;  // should be false
	vector<vector<clause_t>> formula7 = { {{7}}, {{17, 19} } };           // p \/ (~p /\ ~q)
	cout << check_if_bagged_formula_is_simplified(formula7, 10) << endl;  // should be false
}

void Solver::run_tautology_DE_unit_tests()
{
	unordered_map<inv_t, bool, SetVectorHash> curr_checked_tautology_dict;
	inv_t formula0 = { {0, 2}, {0, 12} };                                 // (p /\ q) \/ (p /\ ~q)
	cout << helper.check_if_candidate_inv_is_tautology(formula0, 10, curr_checked_tautology_dict);  // should be false
	inv_t formula1 = { {0, 2}, {10, 12}, {2, 10} };                       // (p /\ q) \/ (~p /\ ~q) \/ (~p /\ q)
	cout << helper.check_if_candidate_inv_is_tautology(formula1, 10, curr_checked_tautology_dict);  // should be false
	inv_t formula2 = { {3}, {13} };                                       // p \/ ~p
	cout << helper.check_if_candidate_inv_is_tautology(formula2, 10, curr_checked_tautology_dict);  // should be true
	inv_t formula3 = { {3}, {17}, {7, 13} };                              // p \/ ~q \/ (q /\ ~p)
	cout << helper.check_if_candidate_inv_is_tautology(formula3, 10, curr_checked_tautology_dict);  // should be true
	inv_t formula4 = { {0, 2}, {10, 12}, {2, 10}, {0, 12} };              // (p /\ q) \/ (~p /\ ~q) \/ (~p /\ q) \/ (p /\ ~q)
	cout << helper.check_if_candidate_inv_is_tautology(formula4, 10, curr_checked_tautology_dict);  // should be true
	inv_t formula5 = { {{7}}, {{17, 19} } };                              // p \/ (~p /\ ~q)
	cout << helper.check_if_candidate_inv_is_tautology(formula5, 10, curr_checked_tautology_dict);  // should be false
}
