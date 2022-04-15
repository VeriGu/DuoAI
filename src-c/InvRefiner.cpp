#include "InvRefiner.h"

string signal_passing_file;

void mysigint(int signum)
{
	signal(SIGINT, mysigint);
	cout << "[child-process] The parant process has finished. Exiting..." << endl;
	exit(0);
}

void mysigchld(int signum)
{
	bool child_has_succeeded = false;
	ifstream in(signal_passing_file);
	if (in)
	{
		string line;
		while (getline(in, line))
		{
			for (char ch : line)
			{
				if (ch == 'c')
				{
					child_has_succeeded = true;
					break;
				}
			}
		}
	}
	if (child_has_succeeded)
	{
		cout << "[main-process] Protocol proved by the child process" << endl;
		exit(0);
	}
	else
	{
		// cout << "[main-process] Child process cannot prove the protocol" << endl;
	}
}

void mysighup(int signum)
{
	cout << "[child-process] Main process has died. Exiting..." << endl;
	exit(0);
}

bool wait_for_child_process(int pid)
{
	int status;
	if (waitpid(pid, &status, 0) > 0) {

		if (WIFEXITED(status) && !WEXITSTATUS(status))
		{
			// cout << "program execution successful" << endl;
		}

		else if (WIFEXITED(status) && WEXITSTATUS(status)) {
			if (WEXITSTATUS(status) == 127) {
				// execv failed
				cout << "execv failed" << endl;
				exit(-1);
			}
			else
			{
				// cout << "program terminated normally, but returned a non-zero status" << endl;
			}
		}
		else
			cout << "program didn't terminate normally" << endl;
	}
	else {
		// waitpid() failed
		cout << "waitpid() failed" << endl;
	}
	return true;
}

void InvRefiner::ivy_check(const string& ivy_file, const string& log_file, bool trace, bool force_complete)
{
	// References: https://www.geeksforgeeks.org/difference-fork-exec/, https://cpp.hotexamples.com/examples/-/-/vfork/cpp-vfork-function-examples.html
	// We use "vfork/exec" rather than the more common "system" and more recommended "fork/exec", because vfork does not double the virtual memory space
	pid_t pid = vfork();

	if (pid == -1) {
		// pid == -1 means error occured
		cout << "can't fork, error occured" << endl;
		exit(EXIT_FAILURE);
	}
	else if (pid == 0) {
		remove(log_file.c_str());
		// redirect output to file, from https://stackoverflow.com/a/2605313
		int fd = open(log_file.c_str(), O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
		dup2(fd, 1);   // make stdout go to file
		dup2(fd, 2);   // make stderr go to file - you may choose to not do this, or perhaps send stderr to another file
		close(fd);     // fd no longer needed - the dup'ed handles are sufficient

		if (trace)
		{
			char* argv_list[] = { (char*)IVY_CHECK_PATH, (char*)"trace=true", (char*)(ivy_file.c_str()), NULL };
			execvp(IVY_CHECK_PATH, argv_list);
		}
		else
		{
			char* argv_list[] = { (char*)IVY_CHECK_PATH, (char*)(ivy_file.c_str()), NULL };
			execvp(IVY_CHECK_PATH, argv_list);
		}
		exit(0);
	}
	else
	{
		if (parallel_instance == Parallel_Instance::bottom_up && !trace && !force_complete)
		{
			std::packaged_task<bool(int)> task(wait_for_child_process);
			std::future<bool> future = task.get_future();
			std::thread thr(std::move(task), pid);
			if (future.wait_for(std::chrono::seconds(IVY_CHECK_SAFETY_TIMEOUT)) != std::future_status::timeout)
			{
				thr.join();
			}
			else
			{
				cout << "Ivy check timeout" << endl;
				bool safety_failed = check_if_safety_fails_in_incomplete_log(default_ivy_log_file);
				if (safety_failed)
				{
					cout << "safety property has already failed in incomplete Ivy log" << endl;
					thr.detach();
					return;
				}
				else thr.join();
			}
		}
		else
		{
			wait_for_child_process(pid);
		}
	}
}

void InvRefiner::parse_inv_file(const string& inv_file, map<int, tuple<vars_t, qalter_t, inv_t>>& inv_map)
{
	ifstream in(inv_file.c_str());
	if (!in)
	{
		cout << "Can't open inv file " << inv_file << endl;
		exit(-1);
	}
	string line;
	while (getline(in, line))
	{
		// one example line  
		// invariant [302] forall R1:round. forall V1:value, V2:value. forall Q1:quorum. exists N1:node. V1 ~= V2 -> (member(N1,Q1) & ~vote(N1,R1,V1)) | (member(N1,Q1) & ~decision(N1,R1,V2))
		if (line.rfind("invariant [", 0) == 0)  // equivalent as line.startswith("invariant") in Python
		{
			vector<string> id_and_inv_str;
			split_string(line.substr(11), ']', id_and_inv_str);
			assert(id_and_inv_str.size() == 2);
			int inv_id = std::stoi(id_and_inv_str[0]);
			const string& inv_str = id_and_inv_str[1];
			vector<string> dot_separated_strings;
			split_string(inv_str, '.', dot_separated_strings);
			assert(int(dot_separated_strings.size()) == num_types + 1);
			vars_t vars(num_types, 0);
			qalter_t qalter(num_types, false);
			for (int type_index = 0; type_index < num_types; type_index++)
			{
				vector<string> comma_separated_strings;
				split_string(dot_separated_strings[type_index], ',', comma_separated_strings);
				vars[type_index] = comma_separated_strings.size();
				if (comma_separated_strings[0].rfind("exists", 0) == 0) qalter[type_index] = true;
				else assert(comma_separated_strings[0].rfind("forall", 0) == 0);
			}
			vector<string> greater_than_separated_strings;
			split_string(dot_separated_strings[num_types], '>', greater_than_separated_strings);
			assert(greater_than_separated_strings.size() <= 2);
			const string& dnf_string = greater_than_separated_strings.size() == 2 ? greater_than_separated_strings[1] : greater_than_separated_strings[0];
			// in the example above, dnf_string = "(member(N1,Q1) & ~vote(N1,R1,V1)) | (member(N1,Q1) & ~decision(N1,R1,V2))"
			inv_t parsed_inv;
			parse_dnf_string(dnf_string, p_to_idx_dict.at(vars), predicates_dict.at(vars).size(), parsed_inv);
			inv_map[inv_id] = std::make_tuple(vars, qalter, parsed_inv);
		}
	}
}

void InvRefiner::parse_dnf_string(const string& dnf_string, const map<string, int>& p_to_idx, int number_predicates, inv_t& parsed_inv)
{
	assert(parsed_inv.size() == 0);
	vector<string> clauses;
	split_string(dnf_string, '|', clauses);
	for (const string& raw_clause : clauses)
	{
		string cleaned_clause;
		remove_matching_parenthesis(raw_clause, cleaned_clause);
		vector<string> raw_literals;
		split_string(cleaned_clause, '&', raw_literals);
		clause_t anded_clause;
		for (const string& raw_literal : raw_literals)
		{
			string cleaned_literal;
			remove_matching_parenthesis(raw_literal, cleaned_literal);
			string predicate;
			bool negated = false;
			if (cleaned_literal[0] == '~')
			{
				predicate = cleaned_literal.substr(1);
				negated = true;
			}
			else
			{
				predicate = cleaned_literal;
			}
			int p_idx = p_to_idx.at(predicate);
			if (negated) p_idx += number_predicates;
			anded_clause.push_back(p_idx);
		}
		std::sort(anded_clause.begin(), anded_clause.end());
		parsed_inv.insert(anded_clause);
	}
}

Ivy_return_status InvRefiner::parse_log(const string& log_file, set<int>& failed_inv_ids)
{
	vector<string> dumb_counterexample_lines;
	string dumb_safety_failed_action;
	return parse_log(log_file, failed_inv_ids, dumb_counterexample_lines, dumb_safety_failed_action);
}

Ivy_return_status InvRefiner::parse_log(const string& log_file, set<int>& failed_inv_ids, string& safety_failed_action)
{
	vector<string> dumb_counterexample_lines;
	return parse_log(log_file, failed_inv_ids, dumb_counterexample_lines, safety_failed_action);
}

Ivy_return_status InvRefiner::parse_log(const string& log_file, set<int>& failed_inv_ids, vector<string>& counterexample_lines)
{
	string dumb_safety_failed_action;
	return parse_log(log_file, failed_inv_ids, counterexample_lines, dumb_safety_failed_action);
}

Ivy_return_status InvRefiner::parse_log(const string& log_file, set<int>& failed_inv_ids, vector<string>& counterexample_lines, string& safety_failed_action)
{
	assert(failed_inv_ids.size() == 0 && counterexample_lines.size() == 0);
	safety_failed_action.clear();
	ifstream in(log_file);
	if (!in) {
		cout << "Cannot open Ivy log file" << endl;
		exit(-1);
	}
	string line;
	bool succeed = false;
	bool in_counterexample = false;
	string curr_action = "";
	while (getline(in, line))
	{
		line = trim_string(line);
		if (line.find("FAIL") != string::npos)
		{
			vector<string> substrings;
			split_string(line, ' ', substrings);
			if (substrings.size() != 6) cout << line << endl;
			assert(substrings.size() == 6);
			int failed_inv = stoi(substrings[3]);
			failed_inv_ids.insert(failed_inv);
			if (failed_inv == SAFETY_PROPERTY_ID && safety_failed_action.empty()) safety_failed_action = curr_action;
		}
		else if (line.size() >= 2 && line.substr(0, 2) == "OK")
		{
			succeed = true;
		}
		else if (line.size() >= 15 && line.substr(11, 4) == "ext:")
		{
			curr_action = line.substr(15);
		}
		else if (line.size() >= 35 && line.substr(0, 35) == "searching for a small model... done")
		{
			in_counterexample = true;
			break;
		}
		else if (line.size() >= 42 && line.substr(0, 42) == "error: Solver produced inconclusive result")
		{
			cout << "Warning! Z3 returns unknown" << endl;
			return Ivy_return_status::unknown;
		}
	}
	if (in_counterexample)
	{
		getline(in, line);
		assert(line[0] == '[');
		while (getline(in, line))
		{
			if (line[0] == ']') break;
			counterexample_lines.push_back(trim_string(line));
		}
	}
	in.close();
	assert(!(succeed && failed_inv_ids.size() > 0));
	if ((!succeed) && (failed_inv_ids.size() == 0))
	{
		cout << "Ivy check failed. Check ivy_check_log.txt for details" << endl;
		exit(-1);
	}
	if (succeed) return Ivy_return_status::ok;
	else return Ivy_return_status::fail;
}

bool InvRefiner::check_if_safety_fails_in_incomplete_log(const string& log_file)
{
	ifstream in(log_file);
	if (!in) {
		cout << "Cannot open Ivy log file" << endl;
		exit(-1);
	}
	string line;
	while (getline(in, line))
	{
		line = trim_string(line);
		if (line.find("FAIL") != string::npos)
		{
			vector<string> substrings;
			split_string(line, ' ', substrings);
			if (substrings.size() != 6) cout << line << endl;
			assert(substrings.size() == 6);
			int failed_inv = stoi(substrings[3]);
			if (failed_inv == SAFETY_PROPERTY_ID) return true;
		}
	}
	in.close();
	return false;
}

void InvRefiner::extract_universal_portion_of_invs_dict(const invs_dict_t& input_invs_dict, invs_dict_t& output_invs_dict)
{
	assert(output_invs_dict.empty());
	for (const auto& it : input_invs_dict)
	{
		const vars_t& vars = it.first;
		for (const auto& it2 : it.second)
		{
			const qalter_t& qalter = it2.first;
			const inv_set_t& inv_set = it2.second;
			if (qalter == qalter_t(num_types, false))
			{
				output_invs_dict[vars][qalter] = inv_set;
			}
		}
	}
}

void InvRefiner::pretty_print_forall_inv(const vars_t& vars, const inv_t& inv)
{
	// help debugging
	const vector<string>& predicates = predicates_dict.at(vars);
	int number_predicates = predicates.size();
	vector<string> fragments;
	for (const clause_t& clause : inv)
	{
		if (clause[0] < number_predicates) fragments.push_back(predicates[clause[0]]);
		else fragments.push_back("~" + predicates[clause[0] - number_predicates]);
	}
	string joined_string;
	join_string(fragments, " | ", joined_string);
	cout << joined_string << endl;
}

void InvRefiner::check_inv_on_countereg(const inst_t& inst, const string& csv_file, const string& inv_file)
{
	auto check_inv_on_countereg_start_time = time_now();
	vector<string> inst_predicates;
	DataMatrix data_mat{ NULL, 0, 0 };
	cout << "In check_inv_on_countereg" << endl;
	read_trace(csv_file, inst_predicates, data_mat);
	add_negation(data_mat);
	cout << "read_trace finished in check_inv_on_countereg" << endl;
	assert(inst_predicates == inst_predicates_dict.at(inst));
	map<int, tuple<vars_t, qalter_t, inv_t>> inv_map;
	parse_inv_file(inv_file, inv_map);
	cout << "inv file parsed in check_inv_on_countereg" << endl;
	for (map<int, tuple<vars_t, qalter_t, inv_t>>::const_iterator it = inv_map.begin(); it != inv_map.end(); it++)
	{
		int inv_id = it->first;
		const vars_t& vars = std::get<0>(it->second);
		const qalter_t& qalter = std::get<1>(it->second);
		const inv_t& inv = std::get<2>(it->second);
		vector<bool> is_unique_ordered;
		qalter_to_unique_ordered(qalter, is_unique_ordered);
		const map<vector<int>, vector<int>>& column_indices_each_mapping = column_indices_dict.at(vars).at(inst).at(is_unique_ordered);
		bool inv_hold_curr_inst = check_if_inv_on_csv(vars, qalter, inst, inv, data_mat, column_indices_each_mapping) == INV_HOLD_ON_CSV;
		if (!inv_hold_curr_inst)  // if inv does not hold on the counterexample, then it is a valid inv to make this counterexample no longer valid
		{
			cout << inv_id << endl;
		}
	}
	auto check_inv_on_countereg_end_time = time_now();
	int check_inv_on_countereg_time = time_diff(check_inv_on_countereg_end_time, check_inv_on_countereg_start_time);
	cout << "check_inv_on_countereg_time: " << check_inv_on_countereg_time << endl;
}

bool InvRefiner::top_down_auto_refine()
{
	return(top_down_refine(invs_dict_t(), invs_dict, default_output_ivy_inv_file, false) == Top_down_return_status::inductive);
}

bool InvRefiner::bottom_up_auto_refine()
{
	auto bottom_up_start_time = time_now();
	int top_down_steps_total_time = 0, failed_safety_processing_total_time = 0;
	CounterexampleHandler handler(processor, inst_predicates_dict, config);
	separate_core_and_noncore();
	separate_self_inductive_and_highest_literal(true);

	auto separation_end_time = time_now();
	int total_noncore_invs = noncore_invs_vec.size();
	vector<int> noncore_range;  // instead of the <vars, qalter, inv> tuple, we use an integer index to represent a noncore invariant whenever possible
	for (int i = 0; i < total_noncore_invs; i++) noncore_range.push_back(i);
	Top_down_return_status return_status = Top_down_return_status::safety_failed;
	int accumulated_counterexample_count_each_subset_size[MAX_NONCORE + 1];
	int accumulated_runtime_each_subset_size[MAX_NONCORE + 1];
	for (int num_noncore_invs = 1; num_noncore_invs <= MAX_NONCORE; num_noncore_invs++)
	{
		if (!SELF_INDUCTIVE_MAJORITY) throw not_implemented_exception("no self-inductive majority");
		if (num_noncore_invs == 3) separate_self_inductive_and_highest_literal(false);
		int max_non_self_inductive = min2(num_noncore_invs, max2(1, num_noncore_invs / 2));
		for (int non_self_inductive_count = 0; non_self_inductive_count <= max_non_self_inductive; non_self_inductive_count++)
		{
			int self_inductive_count = num_noncore_invs - non_self_inductive_count;
			for (int highest_literal_noncore_count = 0; highest_literal_noncore_count <= min2(num_noncore_invs, MAX_HIGHEST_LITERAL_NONCORE); highest_literal_noncore_count++)
			{
				if (formula_size_increase_times > 0 && highest_literal_noncore_count == 0) continue;  // this has been covered by a smaller formula size
				for (int highest_literal_self_inductive_count = max2(0, highest_literal_noncore_count + self_inductive_count - num_noncore_invs); highest_literal_self_inductive_count <= min2(self_inductive_count, highest_literal_noncore_count); highest_literal_self_inductive_count++)
				{
					int highest_literal_nonself_inductive_count = highest_literal_noncore_count - highest_literal_self_inductive_count;
					int nonhighest_literal_self_inductive_count = self_inductive_count - highest_literal_self_inductive_count;
					int nonhighest_literal_nonself_inductive_count = non_self_inductive_count - highest_literal_nonself_inductive_count;
					vector<vector<int>> highest_self_inductive_combs, nonhighest_self_inductive_combs, highest_nonself_inductive_combs, nonhighest_nonself_inductive_combs;
					safe_calc_combinations(highest_literal_self_inductive, highest_literal_self_inductive_count, highest_self_inductive_combs);
					safe_calc_combinations(nonhighest_literal_self_inductive, nonhighest_literal_self_inductive_count, nonhighest_self_inductive_combs);
					safe_calc_combinations(highest_literal_nonself_inductive, highest_literal_nonself_inductive_count, highest_nonself_inductive_combs);
					safe_calc_combinations(nonhighest_literal_nonself_inductive, nonhighest_literal_nonself_inductive_count, nonhighest_nonself_inductive_combs);
					long long four_sizes[4] = { (long long int)highest_self_inductive_combs.size(), (long long int)nonhighest_self_inductive_combs.size(), (long long int)highest_nonself_inductive_combs.size(), (long long int)nonhighest_nonself_inductive_combs.size() };
					long long int total_full_comb = four_sizes[0] * four_sizes[1] * four_sizes[2] * four_sizes[3];
					for (long long full_comb_index = 0; full_comb_index < total_full_comb; full_comb_index++)
					{
						long long four_indices[4];
						long long index_number = full_comb_index;
						for (int i = 3; i >= 0; i--)
						{
							four_indices[i] = index_number % four_sizes[i];
							index_number = index_number / four_sizes[i];
						}
						vector<int> noncore_comb(num_noncore_invs);
						concatenate_four_vectors(highest_self_inductive_combs[four_indices[0]], nonhighest_self_inductive_combs[four_indices[1]], highest_nonself_inductive_combs[four_indices[2]], nonhighest_nonself_inductive_combs[four_indices[3]], noncore_comb);
						if (full_comb_index % 100 == 0)
						{
							cout << "enumerating the " << full_comb_index << "-th noncore subset " << vec_to_str(noncore_comb) << " of shape " << vec_to_str(vector<int>({ highest_literal_self_inductive_count, nonhighest_literal_self_inductive_count, highest_literal_nonself_inductive_count, nonhighest_literal_nonself_inductive_count })) << endl;
						}
						bool comb_can_exclude_all_ctes = check_if_comb_excludes_all_ctes(noncore_comb);  // true means this subset of noncore invariants can exclude all counterexamples
						if (!comb_can_exclude_all_ctes) continue;

						// now we know noncore_combs can exclude all counterexample seen so far
						cout << "noncore subset " << vec_to_str(noncore_comb) << " excludes all counterexamples" << endl;
						invs_dict_t noncore_comb_invs_dict;
						for (int noncore_index : noncore_comb)
						{
							const auto& inv_triple = noncore_invs_vec.at(noncore_index);
							noncore_comb_invs_dict[std::get<0>(inv_triple)][std::get<1>(inv_triple)].insert(std::get<2>(inv_triple));
						}
						auto top_down_step_start_time = time_now();
						string safety_failed_action;
						return_status = top_down_refine(ucore_invs_dict, noncore_comb_invs_dict, default_output_ivy_inv_file, safety_failed_action, false, noncore_comb);
						auto top_down_step_end_time = time_now();
						top_down_steps_total_time += time_diff(top_down_step_end_time, top_down_step_start_time);
						assert(return_status != Top_down_return_status::inductive_wo_safety);
						if (return_status == Top_down_return_status::inductive)
						{
							cout << "The subset " + vec_to_str(noncore_comb) + " yields an inductive invariant." << endl;
							break;
						}
						else if (return_status == Top_down_return_status::known_to_fail)
						{
							// top-down refinement reached an invariant set which has been shown non-refinable to an inductive invariant set
							cout << "The subset " + vec_to_str(noncore_comb) + " is refined to an invariant set known to fail." << endl;
						}
						else if (return_status == Top_down_return_status::safety_failed)
						{
							auto failed_safety_processing_start_time = time_now();
							cout << "The subset " + vec_to_str(noncore_comb) + " ended with a failed safety property." << endl;
							// select the Ivy file with only the action on which the safety property failed
							string single_export_ivy_file = "runtime/" + problem_name + "/single_export/" + problem_name + "_" + safety_failed_action + ".ivy";
							encode_and_output(single_export_ivy_file, default_output_ivy_inv_file, ucore_invs_dict, noncore_comb_invs_dict, id_to_inv);  // this can be optimized
							ivy_check(default_output_ivy_inv_file, default_ivy_log_file, true);
							set<int> failed_inv_ids;
							vector<string> counterexample_lines;
							parse_log(default_ivy_log_file, failed_inv_ids, counterexample_lines);
							inst_t cte_inst_size;
							DataMatrix data_mat;
							handler.parse_counterexample_lines_into_data_mat(counterexample_lines, cte_inst_size, data_mat);
							cout << "cte_inst_size: " << vec_to_str(cte_inst_size) << endl;
							for (int noncore_index = 0; noncore_index < total_noncore_invs; noncore_index++)
							{
								const auto& inv_triple = noncore_invs_vec.at(noncore_index);
								const vars_t& vars = std::get<0>(inv_triple);
								const qalter_t& qalter = std::get<1>(inv_triple);
								const inv_t& inv = std::get<2>(inv_triple);
								vector<bool> is_unique_ordered;
								qalter_to_unique_ordered(qalter, is_unique_ordered);
								bool inv_hold_on_cte;
								if (column_indices_dict.at(vars).at(cte_inst_size).find(is_unique_ordered) == column_indices_dict.at(vars).at(cte_inst_size).end()) inv_hold_on_cte = true;
								else inv_hold_on_cte = check_if_inv_on_csv(vars, qalter, cte_inst_size, inv, data_mat, column_indices_dict.at(vars).at(cte_inst_size).at(is_unique_ordered)) == INV_HOLD_ON_CSV;
								// cout << "inv_hold_on_cte: " << inv_hold_on_cte << endl;
								if (!inv_hold_on_cte)
								{
									excluding_invs_each_cte[counterexample_count].insert(noncore_index);
								}
							}
							excluding_invs_each_cte[counterexample_count];  // in case not a single noncore invariant can invalidate the counterexamle, this instruction guarantees key counterexample_count exists in the map
							counterexample_count++;
							auto failed_safety_processing_end_time = time_now();
							failed_safety_processing_total_time += time_diff(failed_safety_processing_end_time, failed_safety_processing_start_time);
						}
						else
						{
							cout << "Error! Unknown return status for top-down refinement." << endl;
							exit(-1);
						}
					}
					if (return_status == Top_down_return_status::inductive) break;
				}
				if (return_status == Top_down_return_status::inductive) break;
			}
			if (return_status == Top_down_return_status::inductive) break;
		}
		if (return_status == Top_down_return_status::inductive) break;

		// log current counterexample info before moving on to the larger subset size
		auto curr_subset_size_end_time = time_now();
		accumulated_counterexample_count_each_subset_size[num_noncore_invs] = counterexample_count;
		accumulated_runtime_each_subset_size[num_noncore_invs] = time_diff_in_seconds(curr_subset_size_end_time, separation_end_time);
		ofstream fout2("runtime/" + problem_name + "/bottom_up/" + "summary_by_subset_size.txt");
		fout2 << "accumulated number of counterexamples" << endl;
		for (int i = 1; i <= num_noncore_invs; i++) fout2 << "noncore subset size " << i << ": " << accumulated_counterexample_count_each_subset_size[i] << endl;
		fout2 << endl << "ucore, noncore, highest-literal separation runtime (seconds): " << time_diff_in_seconds(separation_end_time, bottom_up_start_time) << endl;
		fout2 << "accumulated runtime from separation (seconds)" << endl;
		for (int i = 1; i <= num_noncore_invs; i++) fout2 << "noncore subset size " << i << ": " << accumulated_runtime_each_subset_size[i] << endl;
		fout2.close();
		ofstream fout3("runtime/" + problem_name + "/bottom_up/" + "cte_exclusion.txt");
		for (int cte_idx = 0; cte_idx < counterexample_count; cte_idx++)
		{
			fout3 << "counterexample " << cte_idx << endl;
			for (int e : excluding_invs_each_cte[cte_idx]) fout3 << e << " ";
			fout3 << endl;
		}
		fout3.close();
	}

	auto bottom_up_end_time = time_now();
	cout << "memorized invs dicts: " << failed_invs_dicts.size() << endl;
	cout << "bottom-up refinement finished" << endl << endl;
	cout << "bottom-up refinement total time: " << time_diff(bottom_up_end_time, bottom_up_start_time) << endl;
	cout << "- core & noncore calculation time: " << time_diff(separation_end_time, bottom_up_start_time) << endl;
	cout << "- top-down steps total time: " << top_down_steps_total_time << endl;
	cout << "- failed safety property processing total time: " << failed_safety_processing_total_time << endl;
	return(return_status == Top_down_return_status::inductive);
}

bool InvRefiner::auto_refine()
{
	bool success = false;
	// if the user does not specify whether to use top-down or bottom-up refinement, we decide based on the number of candidate invariants involving exists
	if (parallel_instance == Parallel_Instance::top_down_or_bottom_up)
	{
		int total_exists_candidates = 0;
		for (const auto& it1 : invs_dict)
		{
			for (const auto& it2 : it1.second)
			{
				const qalter_t& qalter = it2.first;
				if (qalter != qalter_t(num_types, false)) total_exists_candidates += it2.second.size();
			}
		}
		cout << "total exists candidates: " << total_exists_candidates << endl;
		if (total_exists_candidates <= TOP_DOWN_MAX_INV) parallel_instance = Parallel_Instance::top_down;
		else parallel_instance = Parallel_Instance::bottom_up;
	}
	if (parallel_instance == Parallel_Instance::bottom_up)
	{
		refine_degree = Refine_degree::co_implication;  // the other options have not been sufficiently tested
		success = bottom_up_auto_refine();
		write_success_signal(success, 'b');
	}
	else
	{
		assert(parallel_instance == Parallel_Instance::forall_only || parallel_instance == Parallel_Instance::top_down);
		if (refine_degree == Refine_degree::removal_and_coimpl)
		{
			// run a removal-only refinement and a co-implication refinement in parallel
			// references 1) https://www.geeksforgeeks.org/signals-c-set-2/, 2) https://docs.oracle.com/cd/E19455-01/806-4750/signals-7/index.html
			int pid = fork();
			if (pid == 0)  // child process
			{
				signal(SIGINT, mysigint);  // if the main process succeeds, the child process will receive SIGINT from the main process and exit
				signal(SIGHUP, mysighup);  // if the main process is shut down externally, the child process will receive SIGHUP from Linux kernel and exit
				prctl(PR_SET_PDEATHSIG, SIGHUP);
				refine_degree = Refine_degree::removal_only;
				default_output_ivy_inv_file = default_output_ivy_inv_file.substr(0, default_output_ivy_inv_file.size() - 4) + "_child.ivy";
				default_ivy_log_file = default_ivy_log_file.substr(0, default_ivy_log_file.size() - 4) + "_child.txt";
				cout << "starting removal-only refinement process" << endl;
				success = top_down_auto_refine();
				write_success_signal(success, 'c');
				exit(0);
			}
			else  // parent process
			{
				signal(SIGCHLD, mysigchld);
				refine_degree = Refine_degree::co_implication;
				default_output_ivy_inv_file = default_output_ivy_inv_file.substr(0, default_output_ivy_inv_file.size() - 4) + "_main.ivy";
				default_ivy_log_file = default_ivy_log_file.substr(0, default_ivy_log_file.size() - 4) + "_main.txt";
				cout << "starting co-implication refinement process" << endl;
				success = top_down_auto_refine();
				write_success_signal(success, 'm');
				kill(pid, SIGINT);
			}
		}
		else
		{
			success = top_down_auto_refine();
			write_success_signal(success, 't');
		}
	}
	return(success);
}

bool InvRefiner::auto_enumerate_and_refine()
{
	auto_solve();
	return auto_refine();
}

void InvRefiner::encode_and_output(const string& infile, const string& outfile, const invs_dict_t& invs_dict_to_encode, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	vector<string> str_invs;
	id_to_inv.clear();
	encoder.encode_invs_dict(invs_dict_to_encode, predicates_dict, str_invs, id_to_inv, more_invs);
	encoder.append_invs_ivy(infile, outfile, str_invs);
}

void InvRefiner::encode_and_output(const string& infile, const string& outfile, const vector<tuple<vars_t, qalter_t, inv_t>>& invs_vec_to_encode, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	vector<string> str_invs;
	id_to_inv.clear();
	encoder.encode_invs_vec(invs_vec_to_encode, predicates_dict, str_invs, id_to_inv, more_invs);
	encoder.append_invs_ivy(infile, outfile, str_invs);
}

void InvRefiner::encode_and_output(const string& infile, const string& outfile, const invs_dict_t& known_invs_dict, const invs_dict_t& unknown_invs_dict, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs)
{
	auto joint_invs_dict = known_invs_dict;
	for (const auto& it : unknown_invs_dict)
	{
		const vars_t& vars = it.first;
		for (const auto& it2 : it.second)
		{
			const qalter_t& qalter = it2.first;
			const inv_set_t& inv_set = it2.second;
			joint_invs_dict[vars][qalter].insert(inv_set.begin(), inv_set.end());
		}
	}
	encode_and_output(infile, outfile, joint_invs_dict, id_to_inv, more_invs);
}

void InvRefiner::separate_core_and_noncore()
{
	assert(ucore_invs_dict.empty() && noncore_invs_dict.empty() && ucore_invs_vec.empty() && noncore_invs_vec.empty());
	invs_dict_t forall_invs_dict;
	extract_universal_portion_of_invs_dict(invs_dict, forall_invs_dict);

	// output the enumerated universal invariants without any consideration of inductiveness
	encode_and_output(input_ivy_file, "runtime/" + problem_name + "/bottom_up/" + problem_name + "_forall_invs.ivy", forall_invs_dict, id_to_inv);
	top_down_refine(invs_dict_t(), forall_invs_dict, "runtime/" + problem_name + "/bottom_up/" + problem_name + "_ucore.ivy", true);

	// use set minus to get noncore
	ucore_invs_dict = forall_invs_dict;
	for (auto& it : invs_dict)
	{
		const vars_t& vars = it.first;
		for (auto& it2 : it.second)
		{
			const qalter_t& qalter = it2.first;
			const inv_set_t& original_inv_set = it2.second;
			if (qalter == qalter_t(num_types, false))
			{
				inv_set_t& inv_set = noncore_invs_dict[vars][qalter];
				if (ucore_invs_dict.find(vars) == ucore_invs_dict.end() || ucore_invs_dict.at(vars).find(qalter) == ucore_invs_dict.at(vars).end())
				{
					inv_set = original_inv_set;
				}
				else
				{
					const inv_set_t& ucore_inv_set = ucore_invs_dict.at(vars).at(qalter);
					std::set_difference(original_inv_set.begin(), original_inv_set.end(), ucore_inv_set.begin(), ucore_inv_set.end(), std::inserter(inv_set, inv_set.end()));
				}
			}
			else
			{
				noncore_invs_dict[vars][qalter] = invs_dict[vars][qalter];
			}
		}
	}

	// convert ucore_invs_dict and noncore_invs_dict to ucore_invs_vec and noncore_invs_vec
	for (const auto& it : ucore_invs_dict)
	{
		const vars_t& vars = it.first;
		for (const auto& it2 : it.second)
		{
			const qalter_t& qalter = it2.first;
			const inv_set_t& inv_set = it2.second;
			for (const inv_t& inv : inv_set)
			{
				ucore_invs_vec.push_back(std::make_tuple(vars, qalter, inv));
			}
		}
	}
	for (const auto& it : noncore_invs_dict)
	{
		const vars_t& vars = it.first;
		for (const auto& it2 : it.second)
		{
			const qalter_t& qalter = it2.first;
			const inv_set_t& inv_set = it2.second;
			for (const inv_t& inv : inv_set)
			{
				noncore_invs_vec.push_back(std::make_tuple(vars, qalter, inv));
			}
		}
	}
	encode_and_output(input_ivy_file, "runtime/" + problem_name + "/bottom_up/" + problem_name + "_noncore_candidates.ivy", noncore_invs_vec, id_to_inv);
	calc_extended_invs_dict(ucore_invs_dict);
	for (const vars_t& vars : vars_traversal_order)
	{
		int number_predicates = predicates_dict.at(vars).size();
		for (int first_exists = 0; first_exists <= num_types; first_exists++)  // first_exists == num_types represents forall-only
		{
			const auto& extended_invs = first_exists < num_types ? ucore_deuniqued_extended_invs_dict.at(vars).at(first_exists) : ucore_extended_invs_dict.at(vars);
			unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash> implied_formulas_each_clause;
			helper.calc_base_implied_formulas_each_clause(number_predicates, extended_invs, implied_formulas_each_clause);
			ucore_implied_formulas_each_clause_dict[vars].push_back(implied_formulas_each_clause);
		}
	}

	cout << "Universal inductive core and noncore candidate invariants calculated." << endl;
}

void InvRefiner::separate_self_inductive_and_highest_literal(bool set_all_as_inductive)
{
	int single_noncore_index = check_noncore_self_inductiveness(set_all_as_inductive);
	if (single_noncore_index >= 0)
	{
		// cout << "bottom-up refinement succeeds with a single noncore invariant" << endl;
		// return true;
		cout << "Error! A single noncore invariant can prove the protocol. This should have been discovered before." << endl;
		exit(-1);
	}
	highest_literal_self_inductive.clear();
	nonhighest_literal_self_inductive.clear();
	highest_literal_nonself_inductive.clear();
	nonhighest_literal_nonself_inductive.clear();
	separate_highest_literal_and_not(self_inductive_noncore_indices, highest_literal_self_inductive, nonhighest_literal_self_inductive);
	separate_highest_literal_and_not(non_self_inductive_noncore_indices, highest_literal_nonself_inductive, nonhighest_literal_nonself_inductive);
	ofstream fout1("runtime/" + problem_name + "/bottom_up/" + "literal_inductiveness_count.txt");
	fout1 << "highest_literal_self_inductive: " << highest_literal_self_inductive.size() << endl << "highest_literal_nonself_inductive: " << highest_literal_nonself_inductive.size() << endl << "nonhighest_literal_self_inductive: " << nonhighest_literal_self_inductive.size() << endl << "nonhighest_literal_nonself_inductive: " << nonhighest_literal_nonself_inductive.size() << endl;
	fout1.close();
}

int InvRefiner::check_noncore_self_inductiveness(bool set_all_as_inductive)
{
	// return value: a non-negative number means the protocol is verified during this process, the number is noncore_index which joined with ucore can prove the safety property, otherwise return -1
	self_inductive_noncore_set.clear();
	self_inductive_noncore_indices.clear();
	non_self_inductive_noncore_indices.clear();
	if (LOAD_SELF_INDUCTIVENESS_FROM_FILE) // we can drop this in the final version
	{
		ifstream in("runtime/" + problem_name + "/bottom_up/" + "self_inductive_indices.txt");
		if (!in)
		{
			cout << "Can't open inv file " << problem_name + "_self_inductive_indices.txt" << endl;
			exit(-1);
		}
		string line;
		while (getline(in, line))
		{
			int self_inductive_noncore_index = std::stoi(line);
			self_inductive_noncore_set.insert(self_inductive_noncore_index);
		}
	}
	else
	{
		vector<tuple<vars_t, qalter_t, inv_t>> ucore_plus_one_noncore = ucore_invs_vec;
		int num_ucore_invs = ucore_invs_vec.size();
		int num_noncore_invs = noncore_invs_vec.size();
		if (set_all_as_inductive)
		{
			for (int inv_idx = 0; inv_idx < num_noncore_invs; inv_idx++) self_inductive_noncore_set.insert(inv_idx);
		}
		else
		{
			ucore_plus_one_noncore.push_back(tuple<vars_t, qalter_t, inv_t>());
			vector<int> noncore_indices_to_remove;
			for (int noncore_index = 0; noncore_index < num_noncore_invs; noncore_index++)
			{
				cout << "checking noncore candidates self-inductiveness " << noncore_index << "/" << num_noncore_invs << endl;
				ucore_plus_one_noncore[num_ucore_invs] = noncore_invs_vec[noncore_index];
				encode_and_output(input_ivy_file, default_output_ivy_inv_file, ucore_plus_one_noncore, id_to_inv);
				ivy_check(default_output_ivy_inv_file, default_ivy_log_file, false, true);
				set<int> failed_inv_ids;
				Ivy_return_status ivy_return_status = parse_log(default_ivy_log_file, failed_inv_ids);
				if (ivy_return_status == Ivy_return_status::ok) // universal core conjuncted with this single noncore candidate constitutes an inductive invariant
				{
					return noncore_index;
				}
				else if (ivy_return_status == Ivy_return_status::unknown)  // this invariant triggers Z3.unknown, we should remove it from the noncore set
				{
					// noncore_indices_to_remove.push_back(noncore_index);
				}
				else
				{
					assert(!failed_inv_ids.empty());
					failed_inv_ids.erase(SAFETY_PROPERTY_ID);
					if (failed_inv_ids.empty()) self_inductive_noncore_set.insert(noncore_index);
				}
			}
		}

		ofstream fout("runtime/" + problem_name + "/bottom_up/" + "self_inductive_indices.txt");
		for (int e : self_inductive_noncore_set) fout << e << endl;
		fout.close();
	}

	self_inductive_noncore_indices.assign(self_inductive_noncore_set.begin(), self_inductive_noncore_set.end());
	int total_noncore_invs = noncore_invs_vec.size();
	for (int i = 0; i < total_noncore_invs; i++)
	{
		if (self_inductive_noncore_set.find(i) == self_inductive_noncore_set.end()) non_self_inductive_noncore_indices.push_back(i);
	}
	return(-1);
}

void InvRefiner::separate_highest_literal_and_not(const vector<int>& some_noncore_indices, vector<int>& highest_literal_indices, vector<int>& nonhighest_literal_indices)
{
	assert(highest_literal_indices.empty() && nonhighest_literal_indices.empty());
	if (formula_size_increase_times == 0)
	{
		// max_literal is still at the initial small value, no need to separate out the highest literal noncore candidates
		nonhighest_literal_indices = some_noncore_indices;
		return;
	}
	for (int noncore_index : some_noncore_indices)
	{
		const inv_t& inv = std::get<2>(noncore_invs_vec[noncore_index]);
		int literal_count = 0;
		for (const clause_t& clause : inv) literal_count += clause.size();
		if (literal_count == config.max_literal) highest_literal_indices.push_back(noncore_index);
		else
		{
			assert(literal_count < config.max_literal);
			nonhighest_literal_indices.push_back(noncore_index);
		}
	}
}

void InvRefiner::safe_calc_combinations(const vector<int>& some_noncore_indices, int k, vector<noncore_comb_t>& some_noncore_combs)
{
	assert(some_noncore_combs.empty());
	if (k == 0)
	{
		some_noncore_combs.push_back(noncore_comb_t());
		return;
	}
	if (int(some_noncore_indices.size()) < k) return;
	calc_combinations(some_noncore_indices, k, some_noncore_combs);
}

void InvRefiner::concatenate_four_vectors(const vector<int>& vec1, const vector<int>& vec2, const vector<int>& vec3, const vector<int>& vec4, vector<int>& joined)
{
	// assume that joined.size() == vec1.size() + ... + vec4.size()
	std::copy(vec1.begin(), vec1.end(), joined.begin());
	std::copy(vec2.begin(), vec2.end(), joined.begin() + vec1.size());
	std::copy(vec3.begin(), vec3.end(), joined.begin() + vec1.size() + vec2.size());
	std::copy(vec4.begin(), vec4.end(), joined.begin() + vec1.size() + vec2.size() + vec3.size());
}

void InvRefiner::calc_extended_invs_dict(const invs_dict_t& universal_invs_dict)
{
	// calculate extended_invs_dict and deuniqued_extended_invs_dict, note the base class Solver has private member variables of the same name
	// the new variables calculated here are specific to the universal inductive core
	ucore_extended_invs_dict.clear();
	ucore_deuniqued_extended_invs_dict.clear();
	vector<bool> all_true(num_types, true);
	vector<bool> all_false(num_types, false);
	for (const vars_t& vars : vars_traversal_order)
	{
		// calculate ucore_extended_invs_dict[vars]
		const inv_set_t& inv_set = (universal_invs_dict.find(vars) == universal_invs_dict.end() || universal_invs_dict.at(vars).find(all_false) == universal_invs_dict.at(vars).end()) ? inv_set_t() : universal_invs_dict.at(vars).at(all_false);
		inv_set_t& ucore_extended_invs = ucore_extended_invs_dict[vars];
		int number_predicates = predicates_dict.at(vars).size();
		for (const inv_t& inv : inv_set)
		{
			ucore_extended_invs.insert(inv);
			if (int(inv.size()) < config.max_ored_clauses)
			{
				// right now we only add one more literal
				for (int p = 0; p < number_predicates; p++)
				{
					if (inv.find({ p }) == inv.end())
					{
						inv_t new_inv = inv;
						new_inv.insert({ p });
						add_permuted_candidates(ucore_extended_invs, vars, all_true, new_inv);  // question: shall we add subsets here? See Solver.cpp
						new_inv = inv;
						new_inv.insert({ p + number_predicates });
						add_permuted_candidates(ucore_extended_invs, vars, all_true, new_inv);
					}
				}
			}
		}
		// calculate ucore_deuniqued_extended_invs_dict[vars]
		calc_deuniqued_invs(vars, all_false, ucore_deuniqued_extended_invs_dict[vars]);
		for (const auto& it : lowhighvars_column_indices_dict.at(vars))
		{
			// project to higher vars
			const vars_t& successor = it.first;
			const vector<vector<int>>& column_indices_list = it.second.at(all_true);
			inv_set_t new_extended_invs;
			helper.generalize_invs(ucore_extended_invs_dict.at(vars), column_indices_list, new_extended_invs);
			ucore_extended_invs_dict[successor].insert(new_extended_invs.begin(), new_extended_invs.end());
		}
	}
}

inline void InvRefiner::remove_inv_from_invs_dict(invs_dict_t& input_invs_dict, const vars_t& vars, const qalter_t& qalter, const inv_t& inv)
{
	if (input_invs_dict[vars][qalter].size() == 1)  // inv is the only element
	{
		if (input_invs_dict[vars].size() == 1)  // qalter is the only key
		{
			input_invs_dict.erase(vars);
		}
		else
		{
			input_invs_dict[vars].erase(qalter);
		}
	}
	else
	{
		input_invs_dict[vars][qalter].erase(inv);
	}
}

Top_down_return_status InvRefiner::top_down_refine(const invs_dict_t& known_invs_dict, invs_dict_t& unknown_invs_dict, const string& output_ivy_inv_file, bool is_separation_call, const vector<int>& noncore_comb)
{
	string dumb_safety_failed_action;
	return top_down_refine(known_invs_dict, unknown_invs_dict, output_ivy_inv_file, dumb_safety_failed_action, is_separation_call, noncore_comb);
}

Top_down_return_status InvRefiner::top_down_refine(const invs_dict_t& known_invs_dict, invs_dict_t& unknown_invs_dict, const string& output_ivy_inv_file, string& safety_failed_action, bool is_separation_call, const vector<int>& noncore_comb)
{
	// when used as a complete refinement algorithm, input_invs_dict should be the output of the solver, is_separation_call = false
	// when used as a subprocedure in bottom-up refinement, input_invs_dict should be the current invs_dict maintained by bottom_up_auto_refine(), is_separation_call = true
	// noncore_comb is for debug purpose, see definition in bottom_up_auto_refine()
	bool success = false, safety_property_failed = false, safety_property_removed = false;
	vector<invs_dict_t> unknown_invs_dict_each_step;
	int refine_round_number = 0;
	while (true)
	{
		cout << "refine round " << refine_round_number++ << endl;
		// first check if the current unknown_invs_dict is bound to fail
		if (!is_separation_call && std::find(failed_invs_dicts.begin(), failed_invs_dicts.end(), unknown_invs_dict) != failed_invs_dicts.end())
			// if (failed_invs_dicts.find(unknown_invs_dict) != failed_invs_dicts.end())
		{
			failed_invs_dicts.insert(failed_invs_dicts.end(), unknown_invs_dict_each_step.begin(), unknown_invs_dict_each_step.end());  // todo: change to set
			cout << "Top-down refinement stops early because it reaches a known failed invariant set" << endl;
			return Top_down_return_status::known_to_fail;
		}
		unknown_invs_dict_each_step.push_back(unknown_invs_dict);
		string curr_input_ivy_file = safety_property_removed ? "runtime/" + problem_name + "/bottom_up/" + problem_name + "_nosafety.ivy" : input_ivy_file;
		encode_and_output(curr_input_ivy_file, output_ivy_inv_file, known_invs_dict, unknown_invs_dict, id_to_inv, solver_more_invs);
		ivy_check(output_ivy_inv_file, default_ivy_log_file, false);
		set<int> failed_inv_ids;
		Ivy_return_status ivy_return_status = parse_log(default_ivy_log_file, failed_inv_ids, safety_failed_action);
		success = ivy_return_status == Ivy_return_status::ok;
		safety_property_failed = (failed_inv_ids.find(SAFETY_PROPERTY_ID) != failed_inv_ids.end()) || (ivy_return_status == Ivy_return_status::unknown);
		if (safety_property_failed)
		{
			if (is_separation_call)
			{
				failed_inv_ids.erase(SAFETY_PROPERTY_ID);
				safety_property_removed = true;
			}
			else
			{
				failed_invs_dicts.insert(failed_invs_dicts.end(), unknown_invs_dict_each_step.begin(), unknown_invs_dict_each_step.end());  // todo: change to set
				cout << "Safety property failed. Top-down refinement ends." << endl;
				return Top_down_return_status::safety_failed;
			}
		}
		else if (success)
		{
			if (safety_property_removed)
			{
				cout << "Self-inductive invariant set found (excluding safety property)." << endl;
				return Top_down_return_status::inductive_wo_safety;
			}
			else
			{
				cout << "Protocol verified!" << endl;
				cout << "Inductive invariant written to " + default_output_ivy_inv_file.substr(3) << endl;
				return Top_down_return_status::inductive;
			}
		}

		// main refinement preparation
		if (refine_degree == Refine_degree::co_implication && parallel_instance != Parallel_Instance::bottom_up)
		{
			// calculate ucore_implied_formulas_each_clause_dict
			invs_dict_t holding_forall_invs_dict;  // universal candidate invariants that hold in the latest Ivy check
			extract_universal_portion_of_invs_dict(unknown_invs_dict, holding_forall_invs_dict);
			for (int failed_inv : failed_inv_ids)
			{
				const auto& inv_triple = id_to_inv.at(failed_inv);
				const vars_t& vars = std::get<0>(inv_triple);
				const qalter_t& qalter = std::get<1>(inv_triple);
				const inv_t& inv = std::get<2>(inv_triple);
				if (qalter == qalter_t(num_types, false)) holding_forall_invs_dict[vars][qalter].erase(inv);
			}
			calc_extended_invs_dict(holding_forall_invs_dict);
			ucore_implied_formulas_each_clause_dict.clear();
			for (const vars_t& vars : vars_traversal_order)
			{
				int number_predicates = predicates_dict.at(vars).size();
				for (int first_exists = 0; first_exists <= num_types; first_exists++)  // first_exists == num_types represents forall-only
				{
					const auto& extended_invs = first_exists < num_types ? ucore_deuniqued_extended_invs_dict.at(vars).at(first_exists) : ucore_extended_invs_dict.at(vars);
					unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash> implied_formulas_each_clause;
					helper.calc_base_implied_formulas_each_clause(number_predicates, extended_invs, implied_formulas_each_clause);
					ucore_implied_formulas_each_clause_dict[vars].push_back(implied_formulas_each_clause);
				}
			}
		}

		// main refinement procedure
		for (int failed_inv : failed_inv_ids)
		{
			const auto& inv_triple = id_to_inv.at(failed_inv);
			const vars_t& vars = std::get<0>(inv_triple);
			const qalter_t& qalter = std::get<1>(inv_triple);
			const inv_t& inv = std::get<2>(inv_triple);

			// branch on the refinement strategy used
			if (is_separation_call || refine_degree == Refine_degree::removal_only)  // force removal-only for core/noncore separation
			{
				remove_inv_from_invs_dict(unknown_invs_dict, vars, qalter, inv);
			}
			else if (refine_degree == Refine_degree::co_implication)
			{
				// for now, we implement the refinement for the PQR co-implication relation
				remove_inv_from_invs_dict(unknown_invs_dict, vars, qalter, inv);
				int first_exists = std::find(qalter.begin(), qalter.end(), true) - qalter.begin();
				const auto& implied_formulas_each_clause = ucore_implied_formulas_each_clause_dict.at(vars).at(first_exists);
				int coimplication_refined_invariant_count = 0;
				for (const clause_t& clause : inv)
				{
					// if (implied_formulas_each_clause.find(clause) == implied_formulas_each_clause.end()) continue;
					int single_literal_implied_formulas_counter = 0;
					int clause_size = clause.size();
					for (int i = 0; i < clause_size; i++)  // temporary solution
					{
						int literal_ = clause[i];
						if (implied_formulas_each_clause.find({ literal_ }) == implied_formulas_each_clause.end()) continue;
						const unordered_set<vector<int>, VectorHash>& implied_formulas = implied_formulas_each_clause.at({ literal_ });
						for (const vector<int>& implied_formula : implied_formulas)
						{
							if (implied_formula.size() == 1)  // right now we only replace one literal with a weaker one in the candidate inv
							{
								single_literal_implied_formulas_counter++;
								clause_t new_clause = clause;
								new_clause[i] = implied_formula[0];
								inv_t new_inv = inv;
								new_inv.erase(clause);
								new_inv.insert(new_clause);
								if (first_exists == num_types)  // for universal new_inv, we filter it based on extended_invs, if it can be implied by remaining candidates, we do not add it
								{
									bool implied_by_existing_invariant = false;
									const inv_set_t& curr_extended_invs = ucore_extended_invs_dict.at(vars);
									if (curr_extended_invs.find(new_inv) != curr_extended_invs.end()) implied_by_existing_invariant = true;
									else if (curr_extended_invs.find(inv_t({ implied_formula })) != curr_extended_invs.end()) implied_by_existing_invariant = true;
									else if (implied_formulas_each_clause.find(implied_formula) != implied_formulas_each_clause.end())
									{
										const unordered_set<vector<int>, VectorHash>& reverse_implied_formulas = implied_formulas_each_clause.at(implied_formula);
										// the following means A <==> B, then there is no need to weaken A to B
										if (reverse_implied_formulas.find({ literal_ }) != reverse_implied_formulas.end()) implied_by_existing_invariant = true;
									}
									if (implied_by_existing_invariant) continue;
									vector<clause_t> new_inv_as_vec(new_inv.begin(), new_inv.end());
									for (int num_literal = 2; num_literal < int(new_inv.size()); num_literal++)
									{
										vector<vector<clause_t>> clause_combs;
										calc_combinations(new_inv_as_vec, num_literal, clause_combs);
										for (const vector<clause_t> clause_comb : clause_combs)
										{
											inv_t sub_new_inv(clause_comb.begin(), clause_comb.end());
											if (curr_extended_invs.find(sub_new_inv) != curr_extended_invs.end())
											{
												implied_by_existing_invariant = true;
												break;
											}
										}
										if (implied_by_existing_invariant) break;
									}
									if (implied_by_existing_invariant) continue;
								}
								coimplication_refined_invariant_count++;
								unknown_invs_dict[vars][qalter].insert(new_inv);
								if (qalter == qalter_t(num_types, false) && parallel_instance == Parallel_Instance::forall_only)
								{
									add_permuted_candidates(ucore_extended_invs_dict[vars], vars, qalter_t(num_types, true), new_inv);
								}
							}
						}
					}
				}
				if (coimplication_refined_invariant_count > 0) cout << coimplication_refined_invariant_count << " coimplication refined invariant added" << endl;
			}
			else
			{
				throw not_implemented_exception("full refinement");
			}
		}
		// now we finished one refinement round and get an updated invs_dict
	}
}

bool InvRefiner::check_if_comb_excludes_all_ctes(const vector<int>& noncore_comb)
{
	bool comb_can_exclude_all = true;  // true means this subset of noncore invariants can exclude all counterexamples
	for (int cte = 0; cte < counterexample_count; cte++)
	{
		bool excluding_inv_found = false;  // true means there exists one invariant in noncore_combs that can exclude counterexample cte
		for (int noncore_index : noncore_comb)
		{
			const set<int>& excluding_invs = excluding_invs_each_cte.at(cte);
			if (excluding_invs.find(noncore_index) != excluding_invs.end())
			{
				excluding_inv_found = true;
				break;
			}
		}
		if (!excluding_inv_found)
		{
			comb_can_exclude_all = false;
			// cout << "The subset " + vec_to_str(noncore_comb) + " cannot exclude all counterexamples" << endl;
			break;
		}
	}
	return comb_can_exclude_all;
}

void InvRefiner::find_most_filtering_ctes(int k, vector<int>& cte_indices) const
{
	// select k most filtering counterexamples and write the result to cte_indices
	// by "filtering", we mean there are few invariants that can exclude a counterexample
	assert(cte_indices.empty());
	vector<int> excluding_inv_count_each_cte(counterexample_count);
	for (int cte_idx = 0; cte_idx < counterexample_count; cte_idx++)
	{
		excluding_inv_count_each_cte[cte_idx] = excluding_invs_each_cte.at(cte_idx).size();
	}
	
	for (int round = 0; round < min2(k, counterexample_count); round++)
	{
		int min_index = std::min_element(excluding_inv_count_each_cte.begin(), excluding_inv_count_each_cte.end()) - excluding_inv_count_each_cte.begin();
		cte_indices.push_back(min_index);
		excluding_inv_count_each_cte[min_index] = INT_MAX;
	}
}

void InvRefiner::write_success_signal(bool success, char signal_char)
{
	if (success)  // pass info to parant process via file
	{
		ofstream fout(signal_passing_file.c_str());
		fout << signal_char;
		fout.close();
	}
}
