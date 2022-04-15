#ifndef INVENCODER_H
#define INVENCODER_H

#include "basics.h"
#include "StringProcessor.h"

class InvEncoder
{
	const Config& config;
	const StringProcessor& processor;
	void encode_invs_one_vars(const vars_t& vars, const vector<string>& predicates, const map<qalter_t, inv_set_t>& invs_each_qalter, vector<string>& str_invs, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, int start_idx = 100);
	string construct_prefix_one_vars_and_qalter(const vars_t& vars, const qalter_t& qalter);
public:
	InvEncoder(const Config& config_, const StringProcessor& processor_) : config(config_), processor(processor_) {}
	void encode_invs_dict(const map<vars_t, map<qalter_t, inv_set_t>>& invs_dict, const map<vars_t, vector<string>>& predicates_dict, vector<string>& str_invs, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs);
	void encode_invs_vec(const vector<tuple<vars_t, qalter_t, inv_t>>& invs_vec, const map<vars_t, vector<string>>& predicates_dict, vector<string>& str_invs, map<int, tuple<vars_t, qalter_t, inv_t>>& id_to_inv, const vector<tuple<vars_t, qalter_t, string>>& more_invs);
	void append_invs_ivy(const string& infile, const string& outfile, const vector<string>& str_invs);
};
#endif // INVENCODER_H
