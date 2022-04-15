#include "StringProcessor.h"

void StringProcessor::destruct_predicates_dict_core(const map<vars_t, vector<string>>& input_predicates_dict, map<vars_t, vector<vector<int>>>& output_discretized_predicates_dict, bool sketches_calculated)
{
	assert(output_discretized_predicates_dict.size() == 0);
	for (const auto& it : input_predicates_dict)
	{
		const vars_t& vars = it.first;
		const vector<string>& predicates = it.second;
		int number_predicates = predicates.size();
		for (int p_idx = 0; p_idx < number_predicates; p_idx++)
		{
			const string& predicate = predicates[p_idx];
			vector<vector<int>> occurences_indices;  // first index represents type_index, second index represents number of occurence
			// the final int is the location of the first character after this occurence (in plain words, the index of the number), e.g., in p(N1, N2), the vector for type node is [3,7]
			for (const string& type_abbr : config.type_abbr_list)
			{
				int type_abbr_length = type_abbr.size();
				vector<int> occurences_this_type;
				// find all occurences of a substring in a string, reference https://stackoverflow.com/a/4034809
				size_t pos = predicate.find(type_abbr, 0);
				while (pos != string::npos)
				{
					int number_loc = pos + type_abbr_length;
					if ((pos == 0 || predicate[pos-1] < 'A' || predicate[pos-1] > 'z') && (predicate[number_loc] < 'A' || predicate[number_loc] > 'z'))
					{
						occurences_this_type.push_back(number_loc);
					}
					pos = predicate.find(type_abbr, number_loc + 1);
				}
				occurences_indices.push_back(occurences_this_type);
			}

			map<int, pair<int, int>> occurences_map;  // key: location in the string, first value: type index, second value: number of occurence
			// for connect(E2, N2, N1), sketch = "connect(E?, N?, N?)", number_rep = [2,1,12] (suppose node is ordered before edge)
			string sketch = predicate;
			for (int type_index = 0; type_index < num_types; type_index++)
			{
				const vector<int>& occurences_this_type = occurences_indices[type_index];
				for (int number_idx : occurences_this_type)
				{
					assert(sketch[number_idx] >= '1' && sketch[number_idx] <= '9' && sketch[number_idx] <= '0' + vars[type_index]);
					occurences_map[number_idx] = std::make_pair(type_index, sketch[number_idx] - '0');
					sketch[number_idx] = '?';
				}
			}

			vector<int> number_rep;
			vector<vector<int>> sketch_holes_each_type(num_types);
			int number_rep_idx = 1;  // 0 is reserved for sketch id
			for (const auto& it : occurences_map)
			{
				int type_index = it.second.first;
				int number = it.second.second;
				sketch_holes_each_type[type_index].push_back(number_rep_idx);
				number_rep.push_back(number);
				number_rep_idx++;
			}
			if (sketches_calculated)
			{
				assert(sketch_index_map.find(sketch) != sketch_index_map.end());
				assert(sketches_holes_each_type[sketch_index_map.at(sketch)] == sketch_holes_each_type);
			}
			else
			{
				if (sketch_index_map.find(sketch) == sketch_index_map.end())
				{
					// new sketch
					int sketch_id = sketches.size();
					sketch_index_map[sketch] = sketch_id;
					sketches_holes_each_type.push_back(sketch_holes_each_type);
					sketches.push_back(sketch);
				}
			}
			vector<int> discretized_predicate(number_rep.size() + 1); // the final discretized representation of a predicate is the sketch id + number representation
			discretized_predicate[0] = sketch_index_map.at(sketch);
			std::copy(number_rep.begin(), number_rep.end(), discretized_predicate.begin() + 1);
			assert(discretized_predicate.size() == number_rep.size() + 1);
			output_discretized_predicates_dict[vars].push_back(discretized_predicate);
		}
	}
}

void StringProcessor::reverse_indexing(const map<vars_t, vector<vector<int>>>& input_discretized_predicates_dict, map<vars_t, map<vector<int>, int>>& output_discretized_predicates_index_map)
{
	// given a discrete representation of a predicate, find out its index in the predicate list
	assert(output_discretized_predicates_index_map.size() == 0);
	for (const auto& it : input_discretized_predicates_dict)
	{
		const vars_t& vars = it.first;
		const vector<vector<int>>& discretized_predicates = it.second;
		int number_predicates = discretized_predicates.size();
		for (int p_idx = 0; p_idx < number_predicates; p_idx++)
		{
			const vector<int> discretized_p = discretized_predicates[p_idx];
			output_discretized_predicates_index_map[vars][discretized_p] = p_idx;
		}
	}
}

void StringProcessor::initialize()
{
	num_types = config.type_order.size();
}

vector<vector<int>> StringProcessor::get_discretized_predicates(const vars_t& vars) const
{
	return(discretized_predicates_dict.at(vars));
}

map<vector<int>, int> StringProcessor::get_discretized_inst_predicates_index_map(const inst_t& inst) const
{
	return discretized_inst_predicates_index_map_dict.at(inst);
}

string StringProcessor::parse_predicate_str(const string& predicate_str, vector<string>& predicate_args) const
{
	predicate_args.clear();
	size_t equals_sign = predicate_str.find('=');
	if (equals_sign != string::npos)  // e.g., "N2 = source"
	{
		string left_half = trim_string(predicate_str.substr(0, equals_sign));
		string right_half = trim_string(predicate_str.substr(equals_sign + 1));
		predicate_args.push_back(left_half);
		predicate_args.push_back(right_half);
		return "";
	}
	size_t left_paren = predicate_str.find('(');
	size_t right_paren = predicate_str.find(')');
	if (left_paren == string::npos && right_paren == string::npos)  // e.g., "flag"
	{
		return predicate_str;  // input predicate is a boolean individual
	}
	assert(left_paren >= 0 && right_paren >= 0 && left_paren < right_paren);
	string relation_name = trim_string(predicate_str.substr(0, left_paren));
	string relation_args_str = trim_string(predicate_str.substr(left_paren + 1, right_paren - left_paren - 1));
	assert(trim_string(predicate_str.substr(right_paren + 1)).empty());
	assert(relation_args_str.find_first_of("()") == string::npos);
	split_string(relation_args_str, ',', predicate_args);
	return relation_name;
}

int StringProcessor::parse_predicate_term(const string& predicate_term, int expected_type, Term_Subtype& term_subtype, string& processed_term, vector<string>& function_args) const
{
	size_t left_paren = predicate_term.find('(');
	size_t right_paren = predicate_term.find(')');
	int inferred_type = -1;
	if (left_paren == string::npos && right_paren == string::npos)  
	{
		if (predicate_term[0] >= 'a' && predicate_term[0] <= 'z')  // individual
		{
			term_subtype = Term_Subtype::idv;
			processed_term = predicate_term;
			inferred_type = config.individuals.at(predicate_term);
			if (expected_type >= 0) assert(expected_type == inferred_type);
		}
		else if (predicate_term[0] >= 'A' && predicate_term[0] <= 'Z')  // quantified variable
		{
			term_subtype = Term_Subtype::qvar;
			string type_abbr;
			if (expected_type >= 0)
			{
				type_abbr = config.type_abbr_list[expected_type];
				assert(startswith(predicate_term, type_abbr));
				inferred_type = expected_type;
			}
			else
			{
				for (int type_index = 0; type_index < num_types; type_index++)
				{
					const string& candidate_type_abbr = config.type_abbr_list[type_index];
					if (startswith(predicate_term, candidate_type_abbr))
					{
						if (predicate_term[candidate_type_abbr.size()] <= '9')
						{
							inferred_type = type_index;
							type_abbr = candidate_type_abbr;
							break;
						}
					}
				}
				assert(inferred_type >= 0);
			}
			string suffix = predicate_term.substr(type_abbr.size());
			assert(suffix.size() == 1);
			char arg_char = suffix[0] - 1;  // "N1" will become '0'
			processed_term.assign(1, arg_char);
		}
		else
		{
			cout << "Unparsable predicate_term:" << predicate_term << endl;
			exit(-1);
		}
	}
	else  // function application
	{
		assert(left_paren >= 0 && right_paren >= 0 && left_paren < right_paren);
		string function_name = trim_string(predicate_term.substr(0, left_paren));
		assert(config.functions.find(function_name) != config.functions.end());
		string function_args_str = trim_string(predicate_term.substr(left_paren + 1, right_paren - left_paren - 1));
		assert(trim_string(predicate_term.substr(right_paren + 1)).empty());
		assert(function_args_str.find_first_of("()") == string::npos);
		vector<string> function_args_raw;
		split_string(function_args_str, ',', function_args_raw);
		int num_arg = function_args_raw.size();
		const vector<int>& expected_types = config.functions.at(function_name).first;
		int function_output_type = config.functions.at(function_name).second;
		assert(num_arg == int(expected_types.size()));
		inferred_type = function_output_type;
		term_subtype = Term_Subtype::func;
		processed_term = function_name;
		for (int arg_index = 0; arg_index < num_arg; arg_index++)
		{
			const string& function_arg_raw = function_args_raw[arg_index];
			const string& type_abbr = config.type_abbr_list[expected_types[arg_index]];
			string suffix = function_arg_raw.substr(type_abbr.size());
			assert(suffix.size() == 1);  // right now we assume functions do not apply on individuals
			string arg_str(1, suffix[0] - 1); // "N1" will become "0"
			function_args.push_back(arg_str);
		}
	}
	return(inferred_type);
}

void StringProcessor::parse_predicate_into_rep(const string& predicate_str, PredicateRep& predicateRep) const
{
	vector<string> predicate_args;
	string relation_name = parse_predicate_str(predicate_str, predicate_args);
	if (predicate_args.size() == 0)  // boolean individual
	{
		predicateRep.predicate_type = Predicate_Type::bool_idv;
		predicateRep.relation_name = relation_name;
		return;
	}

	if (relation_name.size() == 0)  // equality
	{
		predicateRep.predicate_type = Predicate_Type::eq;
		predicateRep.relation_name.clear();
		predicateRep.primary_type = -1;
		for (const string& predicate_term : predicate_args)
		{
			Term_Subtype subtype;
			string processed_term;
			vector<string> function_args;
			int type_index = parse_predicate_term(predicate_term, -1, subtype, processed_term, function_args);
			assert(!(predicateRep.primary_type >= 0 && predicateRep.primary_type != type_index));
			predicateRep.primary_type = type_index;
			predicateRep.term_subtypes.push_back(subtype);
			predicateRep.terms.push_back(processed_term);
			predicateRep.functions_args.push_back(function_args);
		}
		assert(predicateRep.primary_type >= 0);
		return;
	}

	bool is_order_predicate = false;
	for (const auto& it : config.total_ordered_types)
	{
		if (it.second == relation_name)  // order predicate
		{
			is_order_predicate = true;
			predicateRep.predicate_type = Predicate_Type::le;
			predicateRep.relation_name.clear();
			predicateRep.primary_type = it.first;
			break;
		}
	}
	if (!is_order_predicate)  // relation predicate
	{
		assert(config.relations.find(relation_name) != config.relations.end());
		predicateRep.predicate_type = Predicate_Type::relation_p;
		predicateRep.relation_name = relation_name;
		predicateRep.primary_type = -1;
	}

	// order predicate and relation predicate share the following block
	const vector<int>& relation_signature = config.relations.at(relation_name);
	assert(predicate_args.size() == relation_signature.size());
	int num_arg = predicate_args.size();
	for (int arg_index = 0; arg_index < num_arg; arg_index++)
	{
		const string& predicate_term = predicate_args[arg_index];
		Term_Subtype subtype;
		string processed_term;
		vector<string> function_args;
		parse_predicate_term(predicate_term, relation_signature[arg_index], subtype, processed_term, function_args);
		predicateRep.term_subtypes.push_back(subtype);
		predicateRep.terms.push_back(processed_term);
		predicateRep.functions_args.push_back(function_args);
	}
}

void StringProcessor::parse_predicates(const vector<string>& predicates, map<string, vector<int>>& var_in_p, map<string, int>& p_to_idx) const
{
	assert(var_in_p.size() == 0);
	assert(p_to_idx.size() == 0);
	int num_predicates = predicates.size();
	regex pattern("[A-Z][A-Z_]*[0-9]*");
	for (int idx = 0; idx < num_predicates; idx++)
	{
		string p = predicates[idx];
		p_to_idx[p] = idx;
		smatch match;
		string remaining_str = p;
		set<string> variables_in_this_p;
		while (regex_search(remaining_str, match, pattern))
		{
			string variable = match.str(0);
			if (variables_in_this_p.find(variable) != variables_in_this_p.end()) {}
			else
			{
				variables_in_this_p.insert(variable);
				var_in_p[variable].push_back(idx);
				var_in_p[variable].push_back(idx + num_predicates);  // ~p
			}
			remaining_str = match.suffix().str();
		}
	}
}

void StringProcessor::remap_predicates(const vector<string>& old_predicates, const map<string, string>& vars_map, vector<string>& new_predicates) const
{
	assert(new_predicates.size() == 0);
	if (vars_map.size() == 0)
	{
		new_predicates = old_predicates;
		return;
	}
	new_predicates.reserve(old_predicates.size());
	vector<string> old_vars;
	for (auto const& imap : vars_map)
	{
		old_vars.push_back(imap.first);
	}
	string pattern_str;
	join_string(old_vars, '|', pattern_str);
	regex pattern(pattern_str);
	smatch match;
	for (const string& p : old_predicates)
	{
		string remaining_str = p;
		string mapped_str;
		while (regex_search(remaining_str, match, pattern))
		{
			// cout << "prefix: " << match.prefix().str() << endl;
			// cout << "matched: " << match.str(0) << endl;
			// cout << "suffix: " << match.suffix().str() << endl;
			string new_var = vars_map.at(match.str(0));
			mapped_str += match.prefix().str() + new_var;
			remaining_str = match.suffix().str();
		}
		mapped_str += remaining_str;
		new_predicates.push_back(mapped_str);
	}
}

void StringProcessor::column_compression(const inst_t& inst, const vector<string>& full_predicates, vector<string>& compressed_predicates)
{
	cout << "Reducing predicates from " << full_predicates.size() << endl;
	compressed_predicates.clear();
	int number_predicates = full_predicates.size();
	map<string, vector<int>> candidate_relations;  // key: relation_name, value: list of predicate indices under this relation
	vector<PredicateRep> predicateReps;
	int max_relation_arity = 0;
	for (const auto& it : config.relations) max_relation_arity = max2(int(it.second.size()), max_relation_arity);  // only compress relation predicates with the highest arity
	vector<int> template_sizes;
	for (const string& type_name : config.type_order)
	{
		template_sizes.push_back(config.template_vars_map.at(type_name).size());
	}

	for (int p_idx = 0; p_idx < number_predicates; p_idx++)
	{
		const string& predicate_str = full_predicates[p_idx];
		PredicateRep predicateRep;
		parse_predicate_into_rep(predicate_str, predicateRep);
		predicateReps.push_back(predicateRep);
		if (predicateRep.predicate_type == Predicate_Type::relation_p)
		{
			const string& relation_name = predicateRep.relation_name;
			if (int(config.relations.at(relation_name).size()) == max_relation_arity)
			{
				candidate_relations[relation_name].push_back(p_idx);
			}
		}
	}

	set<int> p_to_remove;
	vector<bool> type_already_reduced(num_types, false);
	for (const auto& it : candidate_relations)
	{
		const string& relation_name = it.first;
		const vector<int>& p_indices = it.second;
		const vector<int> relation_signature = config.relations.at(relation_name);
		assert(int(relation_signature.size()) == max_relation_arity);
		int expected_num_columns = 1;
		for (int type_index : relation_signature) expected_num_columns *= inst[type_index];
		if (expected_num_columns == int(p_indices.size()))  // if this relation has already been compressed in simulation, we do not futher compress it
		{
			// pick which argument/dimension to compress
			int arg_to_compress = -1;
			for (int arg_index = 0; arg_index < max_relation_arity; arg_index++)
			{
				int arg_type = relation_signature[arg_index];
				if (template_sizes[arg_type] >= 2 && !type_already_reduced[arg_type])
				{
					arg_to_compress = arg_index;
					break;
				}
			}
			// find predicates to remove
			if (arg_to_compress >= 0)
			{
				for (int p_idx : p_indices)
				{
					if (predicateReps[p_idx].terms[arg_to_compress] != "0") p_to_remove.insert(p_idx);
				}
				type_already_reduced[relation_signature[arg_to_compress]] = true;
			}
		}
	}

	for (int p_idx = 0; p_idx < number_predicates; p_idx++)
	{
		if (p_to_remove.find(p_idx) == p_to_remove.end())
		{
			compressed_predicates.push_back(full_predicates[p_idx]);
		}
	}
	cout << "Predicates reduced to " << compressed_predicates.size() << endl;
}

void StringProcessor::reconstruct_var_group(const vars_t& vars, vector<vector<string>>& vars_grouped) const
{
	assert(vars_grouped.size() == 0);
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		const string& type_abbr = config.type_abbrs.at(config.type_order[type_index]);
		vector<string> var_names_one_type;
		construct_vars_vector(type_abbr, vars[type_index], var_names_one_type);
		vars_grouped.push_back(var_names_one_type);
	}
}

void StringProcessor::destruct_predicates_dict(const map<vars_t, vector<string>>& predicates_dict)
{
	destruct_predicates_dict_core(predicates_dict, discretized_predicates_dict, true);
	reverse_indexing(discretized_predicates_dict, discretized_predicates_index_map_dict);
}

void StringProcessor::destruct_inst_predicates_dict(const map<vars_t, vector<string>>& inst_predicates_dict)
{
	destruct_predicates_dict_core(inst_predicates_dict, discretized_inst_predicates_dict, false);
	reverse_indexing(discretized_inst_predicates_dict, discretized_inst_predicates_index_map_dict);
}

int StringProcessor::mapcall(const vars_t& vars, const inst_t& inst, const vector<int>& number_rep, const vector<vector<int>>& mapping_each_type)
{
	vector<int> mapped_number_rep(number_rep.size());
	int sketch_id = number_rep[0];
	mapped_number_rep[0] = sketch_id;
	const auto& sketch_holes_each_type = sketches_holes_each_type[sketch_id];
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		const vector<int>& sketches_holes_this_type = sketch_holes_each_type[type_index];
		const vector<int>& mapping_this_type = mapping_each_type[type_index];
		for (int hole : sketches_holes_this_type)
		{
			mapped_number_rep[hole] = mapping_this_type[number_rep[hole]];
		}
	}
	// below is just a safe way for "return discretized_inst_predicates_index_map_dict.at(inst).at(mapped_number_rep);"
	const auto it1 = discretized_inst_predicates_index_map_dict.find(inst);
	assert(it1 != discretized_inst_predicates_index_map_dict.end());
	const map<vector<int>, int>& discretized_inst_predicates_index_map = it1->second;
	const auto it2 = discretized_inst_predicates_index_map.find(mapped_number_rep);
	if (it2 == discretized_inst_predicates_index_map.end()) return INVALID_PREDICATE_COLUMN;
	else return it2->second;
}

string StringProcessor::get_sketch_by_id(int sketch_id)
{
	assert(sketch_id < int(sketches.size()));
	return sketches[sketch_id];
}

bool StringProcessor::parse_inv_str(const string& inv_str_, vars_t& vars, qalter_t& qalter, vector<tuple<string, vector<string>, bool>>& inv_rep)
{
	// return true if parsing succeeds
	string inv_str = trim_string(inv_str_);
	if (startswith(inv_str, "~(") && inv_str[inv_str.size() - 1] == ')')
	{
		qalter = qalter_t(num_types, false);
		vector<string> anded_predicates;
		split_string(inv_str.substr(2, inv_str.size() - 3), '&', anded_predicates);
		vector<set<string>> vars_each_type(num_types);
		set<pair<string, string>> neqs;
		set<tuple<string, string, bool>> les;
		set<tuple<string, vector<string>, bool>> relation_predicates;
		for (string& predicate : anded_predicates)
		{
			predicate = trim_string(predicate);
			bool p_is_negated = false;
			if (predicate[0] == '~')
			{
				p_is_negated = true;
				predicate = trim_string(predicate.substr(1));
			}
			int p_len = predicate.size();
			if (startswith(predicate, "le(") && predicate[p_len - 1] == ')')
			{
				vector<string> two_variables;
				split_string(predicate.substr(3, p_len - 4), ',', two_variables);
				if (two_variables.size() != 2) return false;
				les.insert({ two_variables[0], two_variables[1], p_is_negated });
			}
			else if (predicate.find("~=") != string::npos)
			{
				if (p_is_negated) return false;
				vector<string> two_variables;
				split_string(predicate, "~=", two_variables);
				if (two_variables.size() != 2) return false;
				neqs.insert({ two_variables[0], two_variables[1] });
			}
			else
			{
				bool p_parsed = false;
				for (const auto& it : config.relations)
				{
					const string& relation_name = it.first;
					const vector<int>& relation_signature = it.second;
					if (startswith(predicate, relation_name + "(") && predicate[p_len - 1] == ')')
					{
						string predicate_args_str = predicate.substr(relation_name.size() + 1, p_len - relation_name.size() - 2);
						vector<string> predicate_args;
						split_string(predicate_args_str, ',', predicate_args);
						for (int arg_idx = 0; arg_idx < int(relation_signature.size()); arg_idx++)
						{
							vars_each_type[relation_signature[arg_idx]].insert(predicate_args[arg_idx]);
						}
						relation_predicates.insert({ relation_name, predicate_args, p_is_negated });
						p_parsed = true;
						break;
					}
				}
				if (!p_parsed) return false;
			}
		}

		// calculate a map from quantified variables in the invariant to regularized quantified variables in our system
		map<string, string> var_name_map;
		for (int type_index = 0; type_index < num_types; type_index++)
		{
			vars[type_index] = max2(vars_each_type[type_index].size(), 1);
			vector<string> provided_variables;
			if (config.total_ordered_types.find(type_index) != config.total_ordered_types.end())
			{
				for (const pair<string, string>& neq_pair : neqs)
				{
					if (les.find({ neq_pair.first, neq_pair.second, false }) != les.end())
					{
						les.erase({ neq_pair.first, neq_pair.second, false });
						les.insert({ neq_pair.second, neq_pair.first, true });
					}
					else if (les.find({ neq_pair.second, neq_pair.first, false }) != les.end())
					{
						les.erase({ neq_pair.second, neq_pair.first, false });
						les.insert({ neq_pair.first, neq_pair.second, true });
					}
				}
				for (const tuple<string, string, bool>& le_triple : les)
				{
					if (std::get<2>(le_triple))
					{
						const string& smaller_var = std::get<1>(le_triple);
						const string& greater_var = std::get<0>(le_triple);
						if (provided_variables.size() == 0)
						{
							provided_variables.push_back(smaller_var);
							provided_variables.push_back(greater_var);
						}
						else if (provided_variables[0] == greater_var)
						{
							provided_variables.insert(provided_variables.begin(), smaller_var);
						}
						else if (provided_variables[provided_variables.size() - 1] == smaller_var)
						{
							provided_variables.push_back(greater_var);
						}
						else return false;
					}
				}
			}
			else
			{
				provided_variables.assign(vars_each_type[type_index].begin(), vars_each_type[type_index].end());
			}
			for (int var_idx = 0; var_idx < int(provided_variables.size()); var_idx++)
			{
				var_name_map[provided_variables[var_idx]] = config.type_abbr_list[type_index] + std::to_string(var_idx + 1);
			}
		}

		// map each relation predicate to our regular predicate
		for (const tuple<string, vector<string>, bool>& p_triple : relation_predicates)
		{
			vector<string> mapped_predicate_args;
			for (const string& predicate_arg : std::get<1>(p_triple))
			{
				if (var_name_map.find(predicate_arg) == var_name_map.end()) return false;
				mapped_predicate_args.push_back(var_name_map.at(predicate_arg));
			}
			string mapped_predicate_args_str;
			join_string(mapped_predicate_args, ',', mapped_predicate_args_str);
			string mapped_predicate = std::get<0>(p_triple) + "(" + mapped_predicate_args_str +")";
			inv_rep.push_back({ std::get<0>(p_triple), mapped_predicate_args, !std::get<2>(p_triple) });
		}
		return true;
	}
	return false;
}

string StringProcessor::generate_new_inv_str(const vector<tuple<string, vector<string>, bool>>& inv_rep, const tuple<string, string, bool, bool>& transform)
{
	const string& transform_source = std::get<0>(transform), transform_target = std::get<1>(transform);
	bool transform_source_is_negated = std::get<2>(transform), transform_target_is_negated = std::get<3>(transform);
	vector<string> segments;
	for (const tuple<string, vector<string>, bool>& p_triple : inv_rep)
	{
		tuple<string, vector<string>, bool> new_p_triple = p_triple;
		const string& old_relation_name = std::get<0>(p_triple);
		bool old_is_negated = std::get<2>(p_triple);
		if (old_relation_name == transform_source && old_is_negated == transform_source_is_negated)
		{
			std::get<0>(new_p_triple) = transform_target;
			std::get<2>(new_p_triple) = transform_target_is_negated;
		}
		string joined_args_str;
		join_string(std::get<1>(p_triple), ',', joined_args_str);
		string new_p_str = std::get<2>(new_p_triple) ? "~" : "";
		new_p_str += std::get<0>(new_p_triple) + "(" + joined_args_str + ")";
		segments.push_back(new_p_str);
	}
	string new_inv_str;
	join_string(segments, " | ", new_inv_str);
	return new_inv_str;
}

void StringProcessor::add_checked_invs(vector<tuple<vars_t, qalter_t, string>>& output_vec_invs)
{
	for (const pair<string, int> checked_inv_pair : config.checked_inv_pairs)
	{
		const string& relation_name = checked_inv_pair.first;
		assert(config.relations.find(relation_name) != config.relations.end());
		const vector<int>& relation_signature = config.relations.at(relation_name);
		int arity = relation_signature.size();
		int index = checked_inv_pair.second;
		assert(arity >= 1 && index >= 0 && index < arity);
		int type_index = relation_signature[0];
		for (int i = 0; i < arity; i++) assert(relation_signature[i] == type_index);
		vars_t vars(num_types, 1);
		vars[type_index] = arity + 1;
		qalter_t qalter(num_types, false);
		const string& type_abbr = config.type_abbr_list[type_index];
		vector<string> param_range;
		for (int i = 1; i <= arity; i++) param_range.push_back(type_abbr + std::to_string(i));
		string predicate1;
		join_string(param_range, ',', predicate1);
		predicate1 = "~" + relation_name + "(" + predicate1 + ")";
		param_range[index] = type_abbr + std::to_string(arity + 1);
		string predicate2;
		join_string(param_range, ',', predicate2);
		predicate2 = "~" + relation_name + "(" + predicate2 + ")";
		string inv_str = predicate1 + " | " + predicate2;
		output_vec_invs.push_back({ vars, qalter, inv_str });
	}
}
