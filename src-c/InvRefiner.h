#ifndef INVREFINER_H
#define INVREFINER_H

#include "Solver.h"
#include "CounterexampleHandler.h"
#include <future>
#include <thread>
#include <functional>
#include <csignal>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>  
#include <sys/wait.h>
#include <fcntl.h>
#include <sys/types.h>

#define SAFETY_PROPERTY_ID 1000000
#define IVY_CHECK_PATH "/home/me/anaconda3/envs/py2/bin/ivy_check"  // change this to absolute path of ivy_check on your machine
#define SELF_INDUCTIVE_MAJORITY true
#define LOAD_SELF_INDUCTIVENESS_FROM_FILE false  // default: false, turn to true to save self-inductiveness checking time when debugging 
#define TOP_DOWN_MAX_INV 100
#define MAX_NONCORE 6
#define MAX_HIGHEST_LITERAL_NONCORE 1
#define IVY_CHECK_SAFETY_TIMEOUT 300

enum class Parallel_Instance { forall_only, top_down, bottom_up, top_down_or_bottom_up };
enum class Refine_degree { removal_only, co_implication, full_graph, removal_and_coimpl };
enum class Top_down_return_status { inductive, inductive_wo_safety, safety_failed, known_to_fail };
enum class Ivy_return_status { ok, fail, unknown };

void mysigint(int signum);
void mysigchld(int signum);
void mysighup(int signum);
bool wait_for_child_process(int pid);
extern string signal_passing_file;

class InvRefiner :
	public Solver
{
private:
	string default_ivy_log_file;
	invs_dict_t ucore_invs_dict, noncore_invs_dict;
	vector<tuple<vars_t, qalter_t, inv_t>> ucore_invs_vec, noncore_invs_vec;  // noncore_invs_dict and noncore_invs_vec are the same
	set<int> self_inductive_noncore_set;
	vector<int> self_inductive_noncore_indices, non_self_inductive_noncore_indices;
	vector<int> highest_literal_self_inductive, nonhighest_literal_self_inductive, highest_literal_nonself_inductive, nonhighest_literal_nonself_inductive;
	map<int, tuple<vars_t, qalter_t, inv_t>> id_to_inv;
	int counterexample_count;
	map<int, set<int>> excluding_invs_each_cte;  // for each counterexample (index), the noncore invariants that can exclude it
	vector<invs_dict_t> failed_invs_dicts;
	map<vars_t, inv_set_t> ucore_extended_invs_dict;
	map<vars_t, vector<inv_set_t>> ucore_deuniqued_extended_invs_dict; // third index is first deuniqued type
	map<vars_t, vector<unordered_map<clause_t, unordered_set<vector<int>, VectorHash>, VectorHash>>> ucore_implied_formulas_each_clause_dict;
	Refine_degree refine_degree;
	Parallel_Instance parallel_instance;
	void ivy_check(const string& ivy_file, const string& log_file, bool trace, bool force_complete=false);
	void parse_inv_file(const string& inv_file, map<int, tuple<vars_t, qalter_t, inv_t>>& inv_map);
	void parse_dnf_string(const string& dnf_string, const map<string, int>& p_to_idx, int number_predicates, inv_t& parsed_inv);
	Ivy_return_status parse_log(const string& log_file, set<int>& failed_inv_ids);
	Ivy_return_status parse_log(const string& log_file, set<int>& failed_inv_ids, string& safety_failed_action);
	Ivy_return_status parse_log(const string& log_file, set<int>& failed_inv_ids, vector<string>& counterexample_lines);
	Ivy_return_status parse_log(const string& log_file, set<int>& failed_inv_ids, vector<string>& counterexample_lines, string& safety_failed_action);
	bool check_if_safety_fails_in_incomplete_log(const string& log_file);
	void extract_universal_portion_of_invs_dict(const invs_dict_t& input_invs_dict, invs_dict_t& output_invs_dict);
	void pretty_print_forall_inv(const vars_t& vars, const inv_t& inv);
	void separate_core_and_noncore();
	void separate_self_inductive_and_highest_literal(bool set_all_as_inductive);
	int check_noncore_self_inductiveness(bool set_all_as_inductive);
	void separate_highest_literal_and_not(const vector<int>& some_noncore_indices, vector<int>& highest_literal_indices, vector<int>& nonhighest_literal_indices);
	void safe_calc_combinations(const vector<int>& some_noncore_indices, int k, vector<noncore_comb_t>& some_noncore_combs);
	void concatenate_four_vectors(const vector<int>& vec1, const vector<int>& vec2, const vector<int>& vec3, const vector<int>& vec4, vector<int>& joined);
	void calc_extended_invs_dict(const invs_dict_t& universal_invs_dict);
	void remove_inv_from_invs_dict(invs_dict_t& input_invs_dict, const vars_t& vars, const qalter_t& qalter, const inv_t& inv);
	Top_down_return_status top_down_refine(const invs_dict_t& known_invs_dict, invs_dict_t& unknown_invs_dict, const string& output_ivy_inv_file, bool is_separation_call, const vector<int>& noncore_comb = {});
	Top_down_return_status top_down_refine(const invs_dict_t& known_invs_dict, invs_dict_t& unknown_invs_dict, const string& output_ivy_inv_file, string& safety_failed_action, bool is_separation_call, const vector<int>& noncore_comb = {});
	bool check_if_comb_excludes_all_ctes(const vector<int>& noncore_comb);
	void find_most_filtering_ctes(int k, vector<int>& cte_indices) const;
	void write_success_signal(bool success, char signal_char);
public:
	InvRefiner(string problem, Parallel_Instance parallel_instance_, Refine_degree refine_degree_, int template_increase, int num_attempt) : Solver(problem, template_increase, num_attempt, parallel_instance_ == Parallel_Instance::forall_only), counterexample_count(0), refine_degree(refine_degree_), parallel_instance(parallel_instance_)
	{ 
		default_ivy_log_file = "runtime/" + problem_name + "/ivy_check_log" + "_" + (parallel_instance_ == Parallel_Instance::forall_only ? "f" : "e") + std::to_string(template_increase) + ".txt";
		signal_passing_file = "runtime/" + problem_name + "/signals.txt";
	}
	void check_inv_on_countereg(const inst_t& inst, const string& csv_file, const string& inv_file);
	// the top-level calls
	bool top_down_auto_refine();
	bool bottom_up_auto_refine();
	bool auto_refine();
	bool auto_enumerate_and_refine();
	void encode_and_output(const string& infile, const string& outfile, const invs_dict_t& invs_dict_to_encode, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs = {});
	void encode_and_output(const string& infile, const string& outfile, const vector<tuple<vars_t, qalter_t, inv_t>>& invs_vec_to_encode, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs = {});
	void encode_and_output(const string& infile, const string& outfile, const invs_dict_t& known_invs_dict, const invs_dict_t& unknown_invs_dict, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs = {});
};

#endif
