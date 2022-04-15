#include "InvEncoder.h"

void InvEncoder::encode_invs_dict(const map<vars_t, map<qalter_t, inv_set_t>>& invs_dict, const map<vars_t, vector<string>>& predicates_dict, vector<string>& str_invs, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	// encode an entire inv_dict into a vector of strings, each represents an invariant
	// The API is different from the Python version, "use_refined_invs" can be ignored
	// invs_dict maps vars (e.g., ['N1', 'N2', 'K0']) to invariants, each invariant is a vector of indices (e.g., [3,4,7])
	// predicates_dict maps vars to predicates, each predicate is a string (e.g., 'replied(N1,N2)'). The indices [3,4,7] above mean the 3rd,4th,7th predicates here
	assert(str_invs.size() == 0);  // the results will be written into str_invs
	assert(id_to_inv.size() == 0);
	int start_idx = 100;
	for (map<vars_t, map<qalter_t, inv_set_t>>::const_iterator it = invs_dict.begin(); it != invs_dict.end(); it++)
	{
		const vars_t& vars = it->first;
		const map<qalter_t, inv_set_t>& invs_each_qalter = it->second;
		vector<string> str_invs_for_this_vars;
		encode_invs_one_vars(vars, predicates_dict.at(vars), invs_each_qalter, str_invs_for_this_vars, id_to_inv, start_idx);
		str_invs.insert(str_invs.end(), str_invs_for_this_vars.begin(), str_invs_for_this_vars.end());
		start_idx += 100 * (1 + str_invs_for_this_vars.size() / 100);
	}
	for (const tuple<vars_t, qalter_t, string>& more_inv : more_invs)
	{
		string inv_prefix = construct_prefix_one_vars_and_qalter(std::get<0>(more_inv), std::get<1>(more_inv));
		str_invs.push_back("invariant [" + std::to_string(start_idx) + "] " + inv_prefix + " " + std::get<2>(more_inv));
		start_idx++;
	}
}

void InvEncoder::encode_invs_vec(const vector<tuple<vars_t, qalter_t, inv_t>>& invs_vec, const map<vars_t, vector<string>>& predicates_dict, vector<string>& str_invs, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	// this function is less efficient than encode_invs_dict, do not use it often
	assert(str_invs.size() == 0);  // the results will be written into str_invs
	assert(id_to_inv.size() == 0);
	int start_idx = 0;
	for (const auto& inv_triple : invs_vec)
	{
		const vars_t& vars = std::get<0>(inv_triple);
		const qalter_t& qalter = std::get<1>(inv_triple);
		const inv_t& inv = std::get<2>(inv_triple);
		map<qalter_t, inv_set_t> invs_each_qalter;
		invs_each_qalter[qalter].insert(inv);
		vector<string> str_invs_for_this_vars;
		encode_invs_one_vars(vars, predicates_dict.at(vars), invs_each_qalter, str_invs_for_this_vars, id_to_inv, start_idx);
		str_invs.insert(str_invs.end(), str_invs_for_this_vars.begin(), str_invs_for_this_vars.end());
		start_idx ++;
	}
	for (const tuple<vars_t, qalter_t, string>& more_inv : more_invs)
	{
		string inv_prefix = construct_prefix_one_vars_and_qalter(std::get<0>(more_inv), std::get<1>(more_inv));
		str_invs.push_back("invariant [" + std::to_string(start_idx) + "] " + inv_prefix + " " + std::get<2>(more_inv));
		start_idx++;
	}
}

void InvEncoder::encode_invs_one_vars(const vars_t& vars, const vector<string>& predicates, const map<qalter_t, inv_set_t>& invs_each_qalter, vector<string>& str_invs, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, int start_idx)
{
	// called by encode_invs_dict, "prefix" in Python can be ignored
	assert(str_invs.size() == 0);  // the results will be written into str_invs
	vector<string> all_predicates(predicates);
	for (string& p : all_predicates)
	{
		for (const auto& it : config.shadow_relations)
		{
			const string& shadowing_relation = it.first;
			const vector<string>& shadowed_relations = it.second;
			if (startswith(p, shadowing_relation))
			{
				string p_suffix = p.substr(shadowing_relation.size());
				for (const string& shadowed_relation : shadowed_relations)
				{
					p += " | " + shadowed_relation + p_suffix;
				}
				p = "(" + p + ")";
				break;
			}
		}
	}
	int number_predicates = all_predicates.size();
	for (int p_idx = 0; p_idx < number_predicates; p_idx++)
	{
		all_predicates.push_back("~" + all_predicates[p_idx]);
	}
	map<string, vector<int>> var_in_p;
	map<string, int> p_to_idx;
	processor.parse_predicates(predicates, var_in_p, p_to_idx);
	for (map<qalter_t, inv_set_t>::const_iterator it = invs_each_qalter.begin(); it != invs_each_qalter.end(); it++)
	{
		const qalter_t qalter = it->first;
		string prefix = construct_prefix_one_vars_and_qalter(vars, qalter);
		const inv_set_t& invs = it->second;
		for (const inv_t& inv : invs)
		{
			assert(id_to_inv.find(start_idx) == id_to_inv.end());
			id_to_inv[start_idx] = make_tuple(vars, qalter, inv);
			string line = "invariant [" + std::to_string(start_idx++) + "] ";
			line += prefix;

			vector<string> clauses_as_strings;
			for (const vector<int>& anded_clause : inv)
			{
				vector<string> predicates_one_clause;
				for (const int& e : anded_clause)
				{
					predicates_one_clause.push_back(all_predicates[e]);
				}
				string one_clause_joined;
				join_string(predicates_one_clause, " & ", one_clause_joined);
				if (anded_clause.size() >= 2) one_clause_joined = "(" + one_clause_joined + ")";
				clauses_as_strings.push_back(one_clause_joined);
			}
			
			string clauses_joined;
			join_string(clauses_as_strings, " | ", clauses_joined);
			line += clauses_joined;
			str_invs.push_back(line);
		}
	}
}

string InvEncoder::construct_prefix_one_vars_and_qalter(const vars_t& vars, const qalter_t& qalter)
{
	string prefix;
	vector<bool> is_unique_ordered;
	qalter_to_unique_ordered(qalter, is_unique_ordered);
	vector<vector<string>> vars_grouped;
	processor.reconstruct_var_group(vars, vars_grouped);
	int num_types = config.type_order.size();

	for (int type_index = 0; type_index < num_types; type_index++)
	{
		const string& type_name = config.type_order[type_index];
		string quantifier_decl;
		if (qalter[type_index])
			quantifier_decl = "exists ";
		else
			quantifier_decl = "forall ";
		const vector<string>& var_names = vars_grouped[type_index];
		for (int i = 0; i < vars[type_index]; i++)
		{
			quantifier_decl += var_names[i] + ":" + type_name;
			if (i == vars[type_index] - 1) quantifier_decl += ". ";
			else quantifier_decl += ", ";
		}
		prefix += quantifier_decl;
	}

	vector<string> prefix_segments;
	/* TODO-long-term: support one-to-one
	if (config.one_to_one_exists && config.one_to_one.size() > 0)
	{
		vector<string> pairs;
		for (const auto& x : var_in_p)
		{
			string var = x.first;
			if (config.one_to_one.count(var) > 0)
			{
				pairs.push_back(config.one_to_one_f + "(" + var + ")=" + config.one_to_one[var]);
			}
		}
		string s_join;
		join_string(pairs, " & ", s_join);
		prefix_segments.push_back(s_join);
	}
	*/
	for (int type_index = 0; type_index < num_types; type_index++)
	{
		const vector<string>& group = vars_grouped[type_index];
		assert(group.size() > 0);
		vector<string> pairs;
		if (is_unique_ordered[type_index])
		{
			if (config.total_ordered_types.find(type_index) != config.total_ordered_types.end() && config.total_ordered_types.at(type_index) != "")
			{
				const string& order_relation = config.total_ordered_types.at(type_index);
				for (vars_t::size_type j = 0; j < group.size() - 1; j++)
				{
					pairs.push_back("~" + order_relation + "(" + group[j + 1] + ", " + group[j] + ")");
				}
			}
			else
			{
				for (vars_t::size_type j = 0; j < group.size() - 1; j++)
				{
					for (vars_t::size_type k = j + 1; k < group.size(); k++)
					{
						pairs.push_back(group[j] + " ~= " + group[k]);
					}
				}
			}
			if (pairs.size() > 0)
			{
				string s_join;
				join_string(pairs, " & ", s_join);
				prefix_segments.push_back(s_join);
			}
		}
	}
	if (config.one_to_one_exists)
	{
		assert(vars[config.one_to_one.in_type] == vars[config.one_to_one.out_type]);
		int num_one_to_one_vars = vars[config.one_to_one.in_type];
		for (int i = 0; i < num_one_to_one_vars; i++)
		{
			string func_eq_str = config.one_to_one.func_name + "(" + vars_grouped[config.one_to_one.in_type][i] + ") = " + vars_grouped[config.one_to_one.out_type][i];
			prefix_segments.push_back(func_eq_str);
		}
	}
	if (prefix_segments.size() > 0)
	{
		string prefix_join;
		join_string(prefix_segments, " & ", prefix_join);
		prefix += prefix_join + " -> ";
	}
	return prefix;
}

void InvEncoder::append_invs_ivy(const string& infile, const string& outfile, const vector<string>& str_invs)
{
	// read an Ivy file, and append the invariants to the end
	// learned from https://stackoverflow.com/questions/10195343/copy-a-file-in-a-sane-safe-and-efficient-way
	ifstream source(infile, std::ios::binary);
	ofstream dest(outfile, std::ios::binary);
	dest << source.rdbuf();
	dest << endl;
	for (const string& str_inv : str_invs)
	{
		dest << str_inv << endl;
	}
}
