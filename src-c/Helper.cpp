#include "Helper.h"

void Helper::extract_exists_vars(const vars_t& vars, const qalter_t& qalter, map<int, int>& exists_type_to_varnum_map, vector<int>& exists_type_list, vector<string>& exists_vars, vector<int>& leading_forall_vars)
{
	assert(exists_vars.size() == 0);
	assert(exists_type_to_varnum_map.size() == 0);
	assert(exists_type_list.size() == 0);
	assert(leading_forall_vars.size() == 0);
	int num_types = config.type_order.size();
	for (int i = 0; i < num_types; i++)
	{
		if (qalter[i]) // this type is existentially quantified
		{
			exists_type_to_varnum_map[i] = vars[i];
			exists_type_list.push_back(i);
			const string& type_abbr = config.type_abbrs.at(config.type_order[i]);
			for (int j = 1; j <= vars[i]; j++)
			{
				exists_vars.push_back(type_abbr + std::to_string(j));
			}
		}
	}
	if (exists_type_list.size() == 0) leading_forall_vars = vars;
	else
	{
		for (int i = 0; i < exists_type_list[0]; i++) leading_forall_vars.push_back(vars[i]);
	}
}

bool Helper::bfs_check_connectivity(const vector<set<int>>& edges, const clause_t& candidate_clause, vector<clause_t>& connected_components)
{
	// edges is the graph represented by adjacency list, candidate_clause is a subset of nodes
	// if the nodes are not connected, we record the connected components
	bool graph_connected = true;
	queue<int> discovered;
	discovered.push(candidate_clause[0]);
	set<int> remaining;
	vector<int> burned;
	for (vector<int>::const_iterator it = candidate_clause.begin() + 1; it != candidate_clause.end(); it++)
	{
		remaining.insert(*it);
	}
	while (remaining.size() > 0)
	{
		if (discovered.size() == 0)
		{
			graph_connected = false;
			// burned now forms a connected component, remaining is the new graph to start with
			connected_components.push_back(burned);
			burned.clear();
			int new_node_to_explore = *remaining.begin();
			discovered.push(new_node_to_explore);
			remaining.erase(new_node_to_explore);
		}
		int node_to_explore = discovered.front();
		discovered.pop();
		const set<int>& curr_set = edges[node_to_explore];
		vector<int> newly_connected_nodes;
		for (int node : remaining)
		{
			if (curr_set.find(node) != curr_set.end())
			{
				newly_connected_nodes.push_back(node);
			}
		}
		for (int node : newly_connected_nodes)
		{
			discovered.push(node);
			remaining.erase(node);
		}
		burned.push_back(node_to_explore);
	}
	if (!graph_connected)
	{
		// move discovered elements to burned and form the last connected component
		while (!discovered.empty())
		{
			burned.push_back(discovered.front());
			discovered.pop();
		}
		connected_components.push_back(burned);
	}
	return graph_connected;
}

void Helper::calc_anded_clauses(int number_predicates, const map<string, vector<int>>& var_in_p, const vector<string>& exists_vars, vector<vector<clause_t>>& anded_clauses, vector<map<clause_t, vector<clause_t>>>& connected_components_dicts)
{
	anded_clauses.resize(config.max_anded_literals + 1);
	connected_components_dicts.resize(config.max_anded_literals + 1);
	// build the graph, node represents predicate, add edge between nodes iff predicates share an existentially quantified variable
	vector<set<int>> edges(number_predicates);
	for (const string& exists_var : exists_vars)
	{
		const vector<int>& p_indices = var_in_p.at(exists_var);
		int num_p = p_indices.size();
		for (int i = 0; i < num_p; i += 2)  // var_in_p includes both p and ~p. ~p always follows p. ~p is not needed for now
		{
			for (int j = i + 2; j < num_p; j += 2)
			{
				edges[p_indices[i]].insert(p_indices[j]);
				edges[p_indices[j]].insert(p_indices[i]);
			}
		}
	}
	
	vector<int> range_number_predicates(number_predicates);
	for (int i = 0; i < number_predicates; i++) range_number_predicates[i] = i;
	for (int num_terms = 1; num_terms <= config.max_anded_literals; num_terms++)
	{
		vector<clause_t> candidate_clauses;
		// enumerate anded_clauses, does not include negation
		calc_combinations(range_number_predicates, num_terms, candidate_clauses);
		vector<vector<int>> p_notp_pairs(num_terms);
		for (int i = 0; i < num_terms; i++) p_notp_pairs[i].resize(2);
		unsigned two_to_num_terms = 1;
		for (int i = 0; i < num_terms; i++) two_to_num_terms *= 2;
		for (const clause_t& candidate_clause : candidate_clauses)
		{
			vector<clause_t> connected_components;
			bool connected = bfs_check_connectivity(edges, candidate_clause, connected_components);
			if (connected)
			{
				// add negations
				for (int i = 0; i < num_terms; i++)
				{
					p_notp_pairs[i][0] = candidate_clause[i];
					p_notp_pairs[i][1] = candidate_clause[i] + number_predicates;
				}
				vector<clause_t> clauses_including_negation = cart_product(p_notp_pairs);
				for (clause_t& clause : clauses_including_negation)
				{
					std::sort(clause.begin(), clause.end());  // each anded_clause is sorted
					anded_clauses[num_terms].push_back(clause);
				}
			}
			else
			{
				map<int, pair<int, int>> p_index_pair_in_connected_components_dict;  // a reverse index, 9 -> (3,2) means predicate #9 is the 2nd element of the 3rd connected component
				int num_connected_componented = connected_components.size();
				for (int i = 0; i < num_connected_componented; i++)
				{
					int this_component_size = connected_components[i].size();
					for (int j = 0; j < this_component_size; j++)
					{
						p_index_pair_in_connected_components_dict[connected_components[i][j]] = std::make_pair(i, j);
					}
				}
				vector<bool> negated_each_p(num_terms);
				for (unsigned index_number = 0; index_number < two_to_num_terms; index_number++)
				{
					for (int i = 0; i < num_terms; i++) negated_each_p[i] = (index_number >> i) & 1U;
					clause_t candidate_clause_copy = candidate_clause;
					vector<clause_t> connected_components_copy = connected_components;
					for (int i = 0; i < num_terms; i++) 
					{
						if (negated_each_p[i])
						{
							const pair<int, int>& p_index_pair = p_index_pair_in_connected_components_dict.at(candidate_clause_copy[i]);
							candidate_clause_copy[i] += number_predicates;
							connected_components_copy[p_index_pair.first][p_index_pair.second] += number_predicates;
						}
					}
					std::sort(candidate_clause_copy.begin(), candidate_clause_copy.end());
					for (vector<int>& one_connected_component : connected_components_copy)
					{
						std::sort(one_connected_component.begin(), one_connected_component.end());
					}
					connected_components_dicts[num_terms][candidate_clause_copy] = connected_components_copy;
				}
			}
		}
		std::sort(anded_clauses[num_terms].begin(), anded_clauses[num_terms].end());
	}
}

void Helper::calc_vars_mapping(int type_index, int in_num, int out_num, bool is_unique_ordered, vector<map<string, string>>& vars_mappings)
{
	assert(vars_mappings.size() == 0);
	const string& type_name = config.type_order[type_index];
	const string& type_abbr = config.type_abbrs.at(type_name);
	bool type_total_ordered = config.total_ordered_types.find(type_index) != config.total_ordered_types.end();
	vector<string> old_group;
	construct_vars_vector(type_abbr, out_num, old_group);
	vector<vector<string>> vars_combs;
	if (is_unique_ordered)
	{
		if (in_num > out_num) return;  // we cannot map N1,N2,N3 to n1,n2 while making variable unique
		if (type_total_ordered)
		{
			calc_combinations(old_group, in_num, vars_combs);
		}
		else
		{
			calc_permutations(old_group, in_num, vars_combs);
		}
	}
	else
	{
		vector<vector<string>> old_group_repeated;
		for (int i = 0; i < in_num; i++)
		{
			old_group_repeated.push_back(old_group);
		}
		vars_combs = cart_product(old_group_repeated);
	}
	vector<string> new_group;
	construct_vars_vector(type_abbr, in_num, new_group);
	for (const vector<string>& vars_comb : vars_combs)
	{
		map<string, string> vars_map;
		for (int i = 0; i < in_num; i++)
		{
			vars_map[new_group[i]] = vars_comb[i];
		}
		vars_mappings.push_back(vars_map);
	}
}

void Helper::calc_vars_self_mapping(int in_num, int out_num, vector<vector<int>>& vars_mappings)
{
	// output variables must be {"N1", "N2", ... "N-out_num"}, {"N1, "N3"} is not allowed
	// total order is not considered
	// example in_num = 3, out_num = 2, then vars_mappings.size() == 6
	// N1 N2 N3 -> N1 N1 N2 | N1 N2 N1 | N2 N1 N1 | N1 N2 N2 | N2 N1 N2 | N2 N2 N1
	// vars_mapping = [[1,1,2], [1,2,1], [2,1,1], [1,2,2], [2,1,2], [2,2,1]]
	assert(vars_mappings.size() == 0);
	assert((in_num >= out_num) && (out_num >= 1));
	queue<pair<vector<int>, set<int>>> mapping_pair_queue;
	set<int> init_missing_vars;
	for (int i = 1; i <= out_num; i++) init_missing_vars.insert(i);
	mapping_pair_queue.push(make_pair(vector<int>(), init_missing_vars));
	while (!mapping_pair_queue.empty())
	{
		const pair<vector<int>, set<int>>& pair_to_expand = mapping_pair_queue.front();
		vector<int> existing_vec = pair_to_expand.first;
		set<int> remaining_set = pair_to_expand.second;
		int existing_length = existing_vec.size();
		mapping_pair_queue.pop();
		if (existing_length + int(remaining_set.size()) == in_num)
		{
			if (existing_length == in_num)
			{
				// we enumerated a valid full vector
				vars_mappings.push_back(existing_vec);
			}
			else
			{
				// we have to fill the suffix with what has been excluded in the prefix, with no place to spare
				vector<int> remaining_vec;
				for (int r : remaining_set) remaining_vec.push_back(r);
				vector<vector<int>> remaining_vec_permutations;
				calc_permutations(remaining_vec, remaining_vec.size(), remaining_vec_permutations);
				for (const vector<int>& remaining_vec_permuted : remaining_vec_permutations)
				{
					vector<int> full_vec = existing_vec;
					full_vec.insert(full_vec.end(), remaining_vec_permuted.begin(), remaining_vec_permuted.end());
					vars_mappings.push_back(full_vec);
				}
			}
		}
		else
		{
			// we can choose anything at the current index
			vector<int> new_existing_vec = existing_vec;
			new_existing_vec.resize(existing_length + 1);
			for (int i = 1; i <= out_num; i++)
			{
				new_existing_vec[existing_length] = i;
				if (remaining_set.find(i) == remaining_set.end())
				{
					mapping_pair_queue.push(make_pair(new_existing_vec, remaining_set));
				}
				else 
				{
					set<int> new_remaining_set = remaining_set;
					new_remaining_set.erase(i);
					mapping_pair_queue.push(make_pair(new_existing_vec, new_remaining_set));
				}
			}
		}
	}
}

void Helper::update_base_implied_formulas_each_clause(const inv_t& base_inv, int number_predicates, unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause) const
{
	vector<int> base_inv_as_ored_literals;
	for (const vector<int>& single_literal_clause : base_inv) base_inv_as_ored_literals.push_back(single_literal_clause[0]);
	int num_terms = base_inv_as_ored_literals.size();
	for (int num_anded_terms = 1; num_anded_terms < num_terms; num_anded_terms++)
	{
		vector<clause_t> anded_terms_list;
		calc_combinations(base_inv_as_ored_literals, num_anded_terms, anded_terms_list);
		for (const clause_t& anded_terms : anded_terms_list)
		{
			vector<int> ored_terms;
			difference_two_sorted_vectors(base_inv_as_ored_literals, anded_terms, ored_terms);
			vector<int> negated_anded_terms(num_anded_terms);
			for (int i = 0; i < num_anded_terms; i++) negated_anded_terms[i] = neg_p(anded_terms[i], number_predicates);
			std::sort(negated_anded_terms.begin(), negated_anded_terms.end());
			base_implied_formulas_each_clause[negated_anded_terms].insert(ored_terms);
		}
	}
}

void Helper::calc_base_implied_formulas_each_clause(int number_predicates, const inv_set_t& base_extended_invs, unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause)
{
	if (config.max_anded_literals > config.max_ored_clauses - 1)
	{
		// cout << "Warning! Some implications between anded clauses cannot be encoded due to a small max_or" << endl;
	}
	for (const inv_t& base_inv : base_extended_invs)
	{
		// base_inv can only have OR but not AND
		update_base_implied_formulas_each_clause(base_inv, number_predicates, base_implied_formulas_each_clause);
	}
}

void Helper::remove_tautology_false_in_anded_clauses(vector<vector<clause_t>>& anded_clauses, int number_predicates, const inv_set_t& base_extended_invs)
{
	if (config.max_anded_literals > config.max_ored_clauses)
	{
		cout << "Warning! Some tautology false anded clauses are not filtered out." << endl;
	}
	vector<vector<clause_t>> original_anded_clauses = anded_clauses;
	anded_clauses.clear();
	for (const vector<clause_t>& original_anded_clauses_one_literal_count : original_anded_clauses)
	{
		vector<clause_t> filtered_anded_clauses_this_literal_count;
		int num_terms = original_anded_clauses_one_literal_count.size() > 0 ? original_anded_clauses_one_literal_count[0].size() : -1;
		for (const clause_t& anded_clause : original_anded_clauses_one_literal_count)
		{
			inv_t negated_anded_clause;
			for (int i = 0; i < num_terms; i++) negated_anded_clause.insert({ neg_p(anded_clause[i], number_predicates) });
			if (base_extended_invs.find(negated_anded_clause) == base_extended_invs.end())  // the anded clause should be considered if its negation is not an invariant
			{
				filtered_anded_clauses_this_literal_count.push_back(anded_clause);
			}
		}
		anded_clauses.push_back(filtered_anded_clauses_this_literal_count);
	}
}

void Helper::sort_anded_clauses_by_base_implication(vector<vector<clause_t>>& anded_clauses, const unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause)
{
	// anded_clauses: anded_clauses[i] (1 <= i <= config.max_and) is the list of "considered" anded clauses with length i
	// by "considered" we mean some anded clauses are not included, such as and-decomposable clauses and in-clause-implication (ICI) redundant clauses
	vector<unordered_set<clause_t, VectorHash>> anded_clauses_as_sets;
	for (const vector<clause_t>& anded_clauses_one_literal_count : anded_clauses)
	{
		unordered_set<clause_t, VectorHash> anded_clauses_one_literal_count_as_set(anded_clauses_one_literal_count.begin(), anded_clauses_one_literal_count.end());
		anded_clauses_as_sets.push_back(anded_clauses_one_literal_count_as_set);
	}
	anded_clauses.clear();
	for (const unordered_set<clause_t, VectorHash>& anded_clauses_set : anded_clauses_as_sets)
	{
		// build the implication DAG, represented as adjacency lists (predecessor and successor)
		unordered_map<clause_t, unordered_set<clause_t, VectorHash>, VectorHash> dag_pred;
		unordered_map<clause_t, unordered_set<clause_t, VectorHash>, VectorHash> dag_succ;
		for (const clause_t& anded_clause : anded_clauses_set)
		{
			dag_pred[anded_clause]; dag_succ[anded_clause];  // make sure the key anded_clause exists in both maps
			int anded_clause_length = anded_clause.size();
			unordered_set<vector<int>, VectorHash> implied_ored_clauses;
			integrate_implied_ored_clauses(base_implied_formulas_each_clause, anded_clause, implied_ored_clauses);
			vector<int> implied_literals;
			for (int literal_ : anded_clause) implied_literals.push_back(literal_);  // p /\ q -> p
			for (const vector<int>& implied_ored_clause : implied_ored_clauses)
			{
				if (implied_ored_clause.size() > 1) continue;  // e.g., p -> q \/ r, but we are building a DAG among anded clauses, there is no place for q \/ r
				implied_literals.push_back(implied_ored_clause[0]);
			}
			std::sort(implied_literals.begin(), implied_literals.end());
			vector<clause_t> implied_anded_clauses;
			calc_combinations(implied_literals, anded_clause_length, implied_anded_clauses);
			for (const clause_t& implied_anded_clause : implied_anded_clauses)
			{
				if (anded_clauses_set.find(implied_anded_clause) != anded_clauses_set.end() && implied_anded_clause != anded_clause)
				{
					// anded_clause can imply implied_anded_clause
					if (dag_succ[implied_anded_clause].find(anded_clause) != dag_succ[implied_anded_clause].end())
					{
						// anded_clause is equivalent to implied_anded_clause, remove existing edge from implied_anded_clause to anded_clause
						dag_succ[implied_anded_clause].erase(anded_clause);
						dag_pred[anded_clause].erase(implied_anded_clause);
					}
					else
					{
						// anded_clause is strictly stronger than implied_anded_clause, add an edge from anded_clause to implied_anded_clause
						dag_succ[anded_clause].insert(implied_anded_clause);
						dag_pred[implied_anded_clause].insert(anded_clause);
					}
				}
			}
		}

		// do a topological sort on the DAG
		vector<clause_t> sorted_anded_clauses;
		sorted_anded_clauses.reserve(anded_clauses_set.size());
		while (dag_pred.size() > 0)
		{
			/*  // for debug
			cout << "printing dag_pred" << endl;
			for (const auto& it : dag_pred)
			{
				const clause_t& clause = it.first;
				assert(clause.size() == 1);
				cout << clause[0] << ": ";
				for (const clause_t& succ : it.second) cout << succ[0] << ' ';
				cout << endl;
			}
			cout << endl;
			*/
			vector<clause_t> no_pred_clauses;
			for (unordered_map<clause_t, unordered_set<clause_t, VectorHash>, VectorHash>::const_iterator it = dag_pred.begin(); it != dag_pred.end(); it++)
			{
				const clause_t& anded_clause = it->first;
				const unordered_set<clause_t, VectorHash>& pred_set = it->second;
				if (pred_set.size() == 0) no_pred_clauses.push_back(anded_clause);
			}
			if (no_pred_clauses.size() == 0)
			{
				// Every clause has a predecessor. Topological sort fails. There must be unique clauses A B s.t. A <=> B /\ A => any_clause
				cout << "Error! Every clause has a predecessor. Topological sort fails." << endl;
				exit(-1);
			}
			for (const clause_t& clause_to_remove : no_pred_clauses)
			{
				sorted_anded_clauses.push_back(clause_to_remove);
				const unordered_set<clause_t, VectorHash>& succ_set = dag_succ[clause_to_remove];
				for (const clause_t& succ : succ_set) dag_pred[succ].erase(clause_to_remove);
				dag_pred.erase(clause_to_remove);
				dag_succ.erase(clause_to_remove);
			}
		}

		assert(sorted_anded_clauses.size() == anded_clauses_set.size());
		anded_clauses.push_back(sorted_anded_clauses);
	}
}

void Helper::integrate_implied_ored_clauses(const unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>& base_implied_formulas_each_clause, const clause_t& anded_clause, unordered_set<vector<int>, VectorHash>& implied_ored_clauses) const
{
	assert(implied_ored_clauses.size() == 0);
	int anded_clause_length = anded_clause.size();
	vector<clause_t> sub_anded_clauses;  // subsets of the anded clause that can fit into max_or
	if (anded_clause_length <= config.max_ored_clauses - 1) sub_anded_clauses.push_back(anded_clause);
	else calc_combinations(anded_clause, config.max_ored_clauses - 1, sub_anded_clauses);
	for (const clause_t& sub_anded_clause : sub_anded_clauses)
	{
		if (base_implied_formulas_each_clause.find(sub_anded_clause) != base_implied_formulas_each_clause.end())
		{
			const unordered_set<vector<int>, VectorHash>& implied_ored_clauses_by_this_sub = base_implied_formulas_each_clause.at(sub_anded_clause);
			implied_ored_clauses.insert(implied_ored_clauses_by_this_sub.begin(), implied_ored_clauses_by_this_sub.end());
		}
	}
}

int Helper::check_if_clause_is_subset_of_any_clause_in_group(const clause_t& clause, const vector<clause_t>& clause_group)
{
	// return index of the first superset clause in group
	// clause = [1,4], clause_group = [[0,4,7], [1,3,4]], return 1
	// clause = [2,3], clause_group = [[0,1,2], [1,3,5]], return -1
	int clause_length = clause.size();
	int clause_group_size = clause_group.size();
	int higher_clause_length = clause_group[0].size();
	for (int i = 0; i < clause_group_size; i++)
	{
		const clause_t& higher_anded_clause = clause_group[i];
		// assume every anded_clause is sorted
		int lower_clause_pointer = 0, higher_clause_pointer = 0;
		bool is_subset = true;
		while (lower_clause_pointer < clause_length)
		{
			if (higher_clause_pointer == higher_clause_length)
			{
				is_subset = false;
				break;
			}
			if (clause[lower_clause_pointer] < higher_anded_clause[higher_clause_pointer])
			{
				is_subset = false;
				break;
			}
			if (clause[lower_clause_pointer] == higher_anded_clause[higher_clause_pointer])
			{
				lower_clause_pointer++;
			}
			higher_clause_pointer++;
		}
		if (is_subset) return i;
	}
	return -1;
}

bool Helper::check_if_clause_can_reduce_clauses_in_group(const clause_t& clause, const vector<clause_t>& clause_group, int number_predicates, clause_t& final_witness, vector<clause_t>& clauses_to_remove)
{
	// clause = [2], clause_group = [[3,4], [5,12]], number_predicates = 10, return true (p \/ (~p /\ q) <=> p \/ q)
	int clause_length = clause.size();
	clause_t negated_clause(clause_length);
	for (int i = 0; i < clause_length; i++) negated_clause[i] = neg_p(clause[i], number_predicates);
	// assume higher_anded_clauses are unique
	map<clause_t, vector<clause_t>> negated_p_seen_each_witness;
	// let's say clause is [15,17] and negated_clause is [5,7], we go through each clause in higher group
	for (const clause_t& higher_anded_clause : clause_group)
	{
		int found_index = -1;
		bool found_no_more_than_once = true;
		for (int negated_p : negated_clause)
		{
			vector<int>::const_iterator it = std::find(higher_anded_clause.begin(), higher_anded_clause.end(), negated_p);
			if (it != higher_anded_clause.end())
			{
				if (found_index >= 0)
				{
					found_no_more_than_once = false;
					break;
				}
				found_index = it - higher_anded_clause.begin();
			}
		}
		if ((found_index >= 0) && (found_no_more_than_once))  // either 5 or 7 (but not both) found in this higher clause
		{
			clause_t witness = higher_anded_clause;
			witness.erase(witness.begin() + found_index);     // witness is now the higher clause with 5 or 7 removed
			negated_p_seen_each_witness[witness].push_back(higher_anded_clause);
			if (int(negated_p_seen_each_witness[witness].size()) == clause_length)
			{
				// both clauses witness + [5] and witness + [7] exist in higher group
				final_witness = witness;
				clauses_to_remove = negated_p_seen_each_witness[witness];
				return true;
			}
		}
	}
	return false;
}

void Helper::calc_DE_simplified_dict(const vector<clause_t>& anded_clauses, const map<int, int>& exists_type_to_varnum_map, const vector<string>& predicates, const map<string, int>& p_to_idx, unordered_map<clause_t, clause_t, VectorHash>& DE_simplified_forms_dict)
{
	assert(DE_simplified_forms_dict.size() == 0);
	if (anded_clauses.size() == 0) return;
	map<string, string> DE_simp_vars_map;  // map all existentially quantified variables (N1,N2,N3) to the the first one (N1)
	for (map<int, int>::const_iterator it = exists_type_to_varnum_map.begin(); it != exists_type_to_varnum_map.end(); it++)
	{
		int type_index = it->first;
		int var_num = it->second;
		if (var_num >= 2)
		{
			vector<string> all_var_names;
			construct_vars_vector(config.type_abbrs.at(config.type_order[type_index]), var_num, all_var_names);
			string first_var_name = config.type_abbrs.at(config.type_order[type_index]) + "1";
			for (int var_index = 1; var_index < var_num; var_index++)
			{
				DE_simp_vars_map[all_var_names[var_index]] = first_var_name;
			}
		}
	}
	vector<string> mapped_predicates;
	processor.remap_predicates(predicates, DE_simp_vars_map, mapped_predicates);
	int num_predicates = predicates.size();
	vector<int> column_indices(2 * num_predicates);
	for (int i = 0; i < num_predicates; i++)
	{
		const string& mapped_p = mapped_predicates[i];
		column_indices[i] = p_to_idx.at(mapped_p);
	}
	for (int i = 0; i < num_predicates; i++)
	{
		column_indices[i + num_predicates] = column_indices[i] + num_predicates;
	}

	// now we know after N1 N2 E1 E2-> N1 N1 E1 E1 mapping, the indices of the new predicates in the old predicate list
	// we precompute the mapped result of each anded clause, the resulting clause may be shorter than the original clause
	int num_terms = anded_clauses[0].size();
	clause_t new_clause(num_terms);
	for (const clause_t& anded_clause : anded_clauses)
	{
		set<int> new_clause_as_set;
		for (int i = 0; i < num_terms; i++)
		{
			int mapped_p = column_indices[anded_clause[i]];
			// remove p /\ ~p
			int negated_mapped_p = neg_p(mapped_p, num_predicates);
			if (new_clause_as_set.find(negated_mapped_p) != new_clause_as_set.end()) new_clause_as_set.erase(negated_mapped_p);
			else new_clause_as_set.insert(mapped_p);
		}
		clause_t new_clause(new_clause_as_set.begin(), new_clause_as_set.end());
		std::sort(new_clause.begin(), new_clause.end());
		DE_simplified_forms_dict[anded_clause] = new_clause;
	}
}

bool Helper::check_if_candidate_inv_is_tautology(const inv_t& candidate_inv, int number_predicates, unordered_map<inv_t, bool, SetVectorHash>& curr_checked_tautology_dict)
{
	// e.g., (p /\ q) \/ (p /\ ~q) \/ ~p is a tautology (evaluates to true)
	// we assume p /\ ~p /\ ... does not exist, it should have been simplified in DE_simplified_forms_dicts
	if (curr_checked_tautology_dict.find(candidate_inv) != curr_checked_tautology_dict.end())
		return curr_checked_tautology_dict[candidate_inv];
	vector<vector<clause_t>> clauses_each_literal_number(config.max_anded_literals + 1);
	for (const clause_t& anded_clause : candidate_inv) clauses_each_literal_number[anded_clause.size()].push_back(anded_clause);

	for (int num_terms = 1; num_terms <= config.max_anded_literals; num_terms++)
	{
		const vector<clause_t>& clauses_this_literal_number = clauses_each_literal_number[num_terms];
		for (const clause_t clause : clauses_this_literal_number)
		{
			// first simplify by subset relation
			for (int higher_group_num_terms = num_terms + 1; higher_group_num_terms <= config.max_anded_literals; higher_group_num_terms++)
			{
				const vector<clause_t>& higher_group = clauses_each_literal_number[higher_group_num_terms];
				if (higher_group.size() > 0)
				{
					int index_of_superset_clause = check_if_clause_is_subset_of_any_clause_in_group(clause, higher_group);
					if (index_of_superset_clause >= 0)
					{
						inv_t simplified_candidate_inv = candidate_inv;
						simplified_candidate_inv.erase(higher_group[index_of_superset_clause]);
						bool simplified_inv_is_tautology = check_if_candidate_inv_is_tautology(simplified_candidate_inv, number_predicates, curr_checked_tautology_dict);
						curr_checked_tautology_dict[candidate_inv] = simplified_inv_is_tautology;
						return simplified_inv_is_tautology;
					}
				}
			}
			// second simplify by p \/ (~p /\ q) reduction
			for (int higher_group_num_terms = 1; higher_group_num_terms <= config.max_anded_literals; higher_group_num_terms++)
			{
				const vector<clause_t>& higher_group = clauses_each_literal_number[higher_group_num_terms];
				if (higher_group.size() > 0)
				{
					clause_t witness;
					vector<clause_t> clauses_to_remove;
					bool can_reduce = check_if_clause_can_reduce_clauses_in_group(clause, higher_group, number_predicates, witness, clauses_to_remove);
					if (can_reduce)
					{
						if (witness.size() == 0)  // clause = [1,2], higher_group = [[11],[12]], (p/\q) \/ ~p \/ ~q, this is a tautology
						{
							curr_checked_tautology_dict[candidate_inv] = true;
							return true;
						}
						else
						{
							inv_t simplified_candidate_inv = candidate_inv;
							for (const clause_t clause_to_remove : clauses_to_remove) simplified_candidate_inv.erase(clause_to_remove);
							simplified_candidate_inv.insert(witness);
							bool simplified_inv_is_tautology = check_if_candidate_inv_is_tautology(simplified_candidate_inv, number_predicates, curr_checked_tautology_dict);
							curr_checked_tautology_dict[candidate_inv] = simplified_inv_is_tautology;
							return simplified_inv_is_tautology;
						}
					}
				}
			}
		}
	}
	// third check if after grouping predicates with the same literal(s), if any clause can shorten other clauses
	map<int, vector<vector<clause_t>>> sub_bagged_formula_each_literal;
	map<pair<int, int>, vector<vector<clause_t>>> sub_bagged_formula_each_literal_pair;
	for (int num_terms = 2; num_terms <= config.max_anded_literals; num_terms++)
	{
		const vector<clause_t>& clauses_this_literal_number = clauses_each_literal_number[num_terms];
		for (const clause_t& anded_clause : clauses_this_literal_number)
		{
			for (int i = 0; i < num_terms; i++)
			{
				clause_t new_clause = anded_clause;
				new_clause.erase(new_clause.begin() + i);
				sub_bagged_formula_each_literal[anded_clause[i]].resize(config.max_anded_literals);
				sub_bagged_formula_each_literal[anded_clause[i]][num_terms - 1].push_back(new_clause);
			}
			if (num_terms >= 3)  // double-literal clause will become none after literal-pair grouping, does not need consideration
			{
				for (int i = 0; i < num_terms; i++)
				{
					for (int j = i + 1; j < num_terms; j++)
					{
						clause_t new_clause = anded_clause;
						new_clause.erase(new_clause.begin() + i);
						new_clause.erase(new_clause.begin() + j - 1);
						sub_bagged_formula_each_literal_pair[std::make_pair(anded_clause[i], anded_clause[j])].resize(config.max_anded_literals - 1);
						sub_bagged_formula_each_literal_pair[std::make_pair(anded_clause[i], anded_clause[j])][num_terms - 2].push_back(new_clause);
					}
				}
			}
		}
	}
	for (map<int, vector<vector<clause_t>>>::const_iterator it = sub_bagged_formula_each_literal.begin(); it != sub_bagged_formula_each_literal.end(); it++)
	{
		int common_literal = it->first;
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
						clause_t witness;
						vector<clause_t> clauses_to_remove;
						bool can_reduce = check_if_clause_can_reduce_clauses_in_group(reducer_clause, reducee_clauses, number_predicates, witness, clauses_to_remove);
						if (can_reduce)
						{
							inv_t simplified_candidate_inv = candidate_inv;
							for (clause_t clause_to_remove : clauses_to_remove)
							{
								insert_in_sorted_vector(clause_to_remove, common_literal);
								simplified_candidate_inv.erase(clause_to_remove);
							}
							insert_in_sorted_vector(witness, common_literal);
							simplified_candidate_inv.insert(witness);
							bool simplified_inv_is_tautology = check_if_candidate_inv_is_tautology(simplified_candidate_inv, number_predicates, curr_checked_tautology_dict);
							curr_checked_tautology_dict[candidate_inv] = simplified_inv_is_tautology;
							return simplified_inv_is_tautology;
						}
					}
				}
			}
		}
	}
	for (map<pair<int, int>, vector<vector<clause_t>>>::const_iterator it = sub_bagged_formula_each_literal_pair.begin(); it != sub_bagged_formula_each_literal_pair.end(); it++)
	{
		const pair<int, int>& common_literal_pair = it->first;
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
						clause_t witness;
						vector<clause_t> clauses_to_remove;
						bool can_reduce = check_if_clause_can_reduce_clauses_in_group(reducer_clause, reducee_clauses, number_predicates, witness, clauses_to_remove);
						if (can_reduce)
						{
							inv_t simplified_candidate_inv = candidate_inv;
							for (clause_t clause_to_remove : clauses_to_remove)
							{
								insert_in_sorted_vector(clause_to_remove, common_literal_pair.first);
								insert_in_sorted_vector(clause_to_remove, common_literal_pair.second);
								simplified_candidate_inv.erase(clause_to_remove);
							}
							insert_in_sorted_vector(witness, common_literal_pair.first);
							insert_in_sorted_vector(witness, common_literal_pair.second);
							simplified_candidate_inv.insert(witness);
							bool simplified_inv_is_tautology = check_if_candidate_inv_is_tautology(simplified_candidate_inv, number_predicates, curr_checked_tautology_dict);
							curr_checked_tautology_dict[candidate_inv] = simplified_inv_is_tautology;
							return simplified_inv_is_tautology;
						}
					}
				}
			}
		}
	}
	curr_checked_tautology_dict[candidate_inv] = false;
	return false;
}

bool Helper::check_if_inv_is_FOCAEI_redundant(const inv_t& candidate_inv, const inv_set_t& extended_invs, const inv_set_t& low_deuniqued_invs)
{
	// redundancy forall_one_clause_and_exists_invariant (FOCAEI)
	// Example 1:    forall X. p(X) \/ q(X)  and  exists X. r(X)  
	// can co-imply  exists X. (p(X) /\ r(X))  \/ q(X)
	// Example 2:    forall X. p1(X) \/ p2(X) \/ q1(X)  and  forall X. p1(X) \/ p2(X) \/ q2(X)  and  exists X. r1(X) /\ r2(X)
	// can co-imply  exists X. p1(X) \/ p2(X)  \/ (q1(X) /\ q2(X) /\ r1(X) /\ r2(X))
	for (const clause_t& anded_clause : candidate_inv)
	{
		int anded_clause_length = anded_clause.size();
		vector<clause_t> other_clauses_in_inv;
		for (const clause_t& other_clause : candidate_inv)
		{
			if (other_clause != anded_clause)
			{
				other_clauses_in_inv.push_back(other_clause);
			}
		}
		vector<vector<int>> forall_ored_invs_one_literal_less = cart_product(other_clauses_in_inv);  // [[ p1(X), p2(X) ]] in ex2
		for (int exists_anded_inv_length = anded_clause_length - 1; exists_anded_inv_length >= 1; exists_anded_inv_length--)
		{
			vector<clause_t> sub_anded_clauses;
			calc_combinations(anded_clause, exists_anded_inv_length, sub_anded_clauses);
			for (const clause_t& exists_anded_inv : sub_anded_clauses)  
			{
				// in ex2, exists_anded_inv = [r1(X), r2(X)], forall_anded_clause = [q1(X), q2(X)]
				clause_t forall_anded_clause;   
				difference_two_sorted_vectors(anded_clause, exists_anded_inv, forall_anded_clause);
				bool this_partition_works = true;
				for (const vector<int>& forall_ored_inv_one_literal_less : forall_ored_invs_one_literal_less)
				{
					// in ex2, [ p1(X), p2(X) ] is the only forall_ored_inv_one_literal_less, q1(X) and q2(X) can be the last literal
					for (int last_literal : forall_anded_clause)
					{
						inv_t forall_ored_inv;
						for (int e : forall_ored_inv_one_literal_less) forall_ored_inv.insert({ e });
						forall_ored_inv.insert({ last_literal });
						if (low_deuniqued_invs.find(forall_ored_inv) == low_deuniqued_invs.end())
						{
							this_partition_works = false;
							break;
						}
					}
					if (!this_partition_works) break;
				}
				if (this_partition_works) return true;
			}
		}
	}
	return false;
}

bool Helper::check_if_inv_within_max_or_and_literal(const inv_t& candidate_inv) const
{
	if (int(candidate_inv.size()) > config.max_ored_clauses) return false;
	int literal_count = 0;
	for (const clause_t& clause : candidate_inv)
	{
		int clause_length = clause.size();
		if (clause_length > config.max_anded_literals) return false;
		literal_count += clause_length;
	}
	if (literal_count > config.max_literal) return false;
	return true;
}

void Helper::generalize_invs(const inv_set_t& pred_extended_invs, const vector<vector<int>>& column_indices_list, inv_set_t& succ_extended_invs)
{
	assert(succ_extended_invs.size() == 0);
	for (const inv_t& inv : pred_extended_invs)
	{
		for (const vector<int>& column_indices : column_indices_list)
		{
			inv_t mapped_inv;
			bool mapping_valid = map_inv_with_column_indices(inv, column_indices, mapped_inv);
			if (mapping_valid) succ_extended_invs.insert(mapped_inv);
		}
	}
}


void Helper::get_all_qalters(int num_types, vector<qalter_t>& all_qalters)
{
	vector<bool> base_choices = { true, false };
	vector<vector<bool>> base_choices_each_type(num_types);
	if (config.max_pos_exists == 0)  // exists can appear at any type
	{
		for (int type_index = 0; type_index < num_types; type_index++) base_choices_each_type[type_index] = base_choices;
	}
	else
	{
		for (int type_index = 0; type_index < num_types; type_index++)
		{
			if (type_index + config.max_pos_exists >= num_types) base_choices_each_type[type_index] = base_choices;
			else base_choices_each_type[type_index] = { false };  // exists cannot appear at this type
		}
	}
	all_qalters = cart_product(base_choices_each_type);
	if (config.one_to_one_exists)
	{
		vector<qalter_t> qalter_to_remove;
		for (qalter_t& qalter : all_qalters)
		{
			if (qalter[config.one_to_one.in_type] != qalter[config.one_to_one.out_type]) qalter_to_remove.push_back(qalter);
		}
		for (const qalter_t& qalter : qalter_to_remove) all_qalters.erase(std::find(all_qalters.begin(), all_qalters.end(), qalter));
	}
}

void Helper::get_all_is_unique_ordereds(int num_types, vector<qalter_t>& all_is_unique_ordereds)
{
	for (int first_exists_type = 0; first_exists_type <= num_types; first_exists_type++)
	{
		if (config.one_to_one_exists && config.one_to_one.out_type == first_exists_type) continue;  // two bijection-related types can only be both forall or both exists
		vector<bool> is_unique_ordered(num_types, false);
		for (int i = 0; i < first_exists_type; i++) is_unique_ordered[i] = true;
		all_is_unique_ordereds.push_back(is_unique_ordered);
	}
}

void Helper::zip_merge_vector_of_map_string(const vector<map<string, string>>& vec_of_map_str_1, const vector<map<string, string>>& vec_of_map_str_2, vector<map<string, string>>& merged_vec_of_map_str)
{
	assert(vec_of_map_str_1.size() == vec_of_map_str_2.size() && merged_vec_of_map_str.empty());
	int num_maps = vec_of_map_str_1.size();
	for (int mapping_idx = 0; mapping_idx < num_maps; mapping_idx++)
	{
		vector<map<string, string>> map_pair_to_merge({ vec_of_map_str_1[mapping_idx], vec_of_map_str_2[mapping_idx] });
		map<string, string> merged_map;
		join_vector_of_maps(map_pair_to_merge, merged_map);
		merged_vec_of_map_str.push_back(merged_map);
	}
}
