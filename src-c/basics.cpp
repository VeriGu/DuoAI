#include "basics.h"

void split_string(const string& str, char delimiter, vector<string>& splitted_results)
{
	stringstream tokenizer(str);
	string temp;
	while (getline(tokenizer, temp, delimiter))
	{
		temp = trim_string(temp);
		if (temp.size() > 0)
		{
			splitted_results.push_back(temp);
		}
	}
}

void split_string(const string& str_, const string& delimiter, vector<string>& splitted_results)
{
	string str = str_;
	size_t pos = 0;
	std::string token;
	while ((pos = str.find(delimiter)) != std::string::npos) {
		token = str.substr(0, pos);
		splitted_results.push_back(trim_string(token));
		str.erase(0, pos + delimiter.length());
	}
	splitted_results.push_back(trim_string(str));
}

void remove_matching_parenthesis(const string& input_string, string& output_string)
{
	int len = input_string.size();
	int max_pair_removed = len / 2;
	int num_pair_removed = 0;
	for (int i = 0; i < max_pair_removed; i++)
	{
		if ((input_string[i] == '(') && (input_string[len - 1 - i] == ')'))
		{
			num_pair_removed++;
		}
		else break;
	}
	output_string = input_string.substr(num_pair_removed, len - 2 * num_pair_removed);
}

void join_string(const vector<string>& v, char c, string& s) {

	s.clear();

	for (vector<string>::const_iterator p = v.begin();
		p != v.end(); ++p) {
		s += *p;
		if (p != v.end() - 1)
			s += c;
	}
}

void join_string(const vector<string>& v, const string& c, string& s) {

	s.clear();

	for (vector<string>::const_iterator p = v.begin();
		p != v.end(); ++p) {
		s += *p;
		if (p != v.end() - 1)
			s += c;
	}
}

int** contiguous_2d_array(int nrow, int ncol)
{
	int** matrix;
	matrix = new int* [nrow];
	matrix[0] = new int[nrow * ncol];

	for (int i = 1; i < nrow; i++) {
		matrix[i] = matrix[i - 1] + ncol;
	}
	return matrix;
}

void difference_two_sorted_vectors(const vector<int>& longer_vec, const vector<int>& shorter_vec, vector<int>& difference_vec)
{
	// difference_vec will be the list of elements in longer_vec but not in shorter_vec
	// assume both longer_vec and shorter_vec are deduplicated
	assert(difference_vec.size() == 0);
	int longer_vec_pointer = 0, shorter_vec_pointer = 0;
	int longer_vec_length = longer_vec.size();
	int shorter_vec_length = shorter_vec.size();
	while (longer_vec_pointer < longer_vec_length)
	{
		if (shorter_vec_pointer == shorter_vec_length) break;
		// we know shorter_vec_pointer < shorter_vec_length
		if (longer_vec[longer_vec_pointer] < shorter_vec[shorter_vec_pointer])
		{
			difference_vec.push_back(longer_vec[longer_vec_pointer]);
			longer_vec_pointer++;
		}
		else
		{
			if (longer_vec[longer_vec_pointer] == shorter_vec[shorter_vec_pointer])
			{
				longer_vec_pointer++;
				shorter_vec_pointer++;
			}
			else
			{
				// we know longer_vec[longer_vec_pointer] > shorter_vec[shorter_vec_pointer]
				shorter_vec_pointer++;
			}
		}
	}
	while (longer_vec_pointer < longer_vec_length)
	{
		difference_vec.push_back(longer_vec[longer_vec_pointer]);
		longer_vec_pointer++;
	}
}

void qalter_to_unique_ordered(const qalter_t& qalter, vector<bool>& is_unique_ordered)
{
	int num_types = qalter.size();
	is_unique_ordered.reserve(num_types);
	bool exists_ever_appeared = false;
	for (bool is_exists : qalter)
	{
		if (is_exists)
		{
			exists_ever_appeared = true;
		}
		is_unique_ordered.push_back(!exists_ever_appeared);
	}
}

void construct_vars_vector(const string& type_abbr, int vars_number, vector<string>& vars_vector)
{
	assert(vars_vector.size() == 0);
	vars_vector.reserve(vars_number);
	for (int i = 1; i <= vars_number; i++)
	{
		vars_vector.push_back(type_abbr + std::to_string(i));
	}
}

void construct_vars_vector(const string& type_abbr, const vector<int>& var_indices, vector<string>& vars_vector)
{
	assert(vars_vector.size() == 0);
	int num_vars = var_indices.size();
	vars_vector.resize(num_vars);
	for (int i = 0; i < num_vars; i++)
	{
		vars_vector[i] = type_abbr + std::to_string(var_indices[i]);
	}
}

void split_n_into_k_numbers_bulk(int N, int K, int R, vector<vector<vector<vector<int>>>>& results)
{
	// put N balls into K buckets, at least one ball per bucket, at most R ball sper bucket, number of balls non-decreasing from first to last bucket
	// results[n][k] (n <= N, k <= K) records the ways to split for the subproblem
	results.resize(N + 1);
	for (int i = 1; i <= N; i++) results[i].resize(K + 1);
	// base case
	for (int n = 1; n <= min2(N,R); n++) results[n][1] = { {n} };
	// dynamic programming
	for (int k = 2; k <= K; k++)
	{
		for (int n = 1; n <= N; n++)
		{
			int lower_bound_last_number = (n + k - 1) / k;
			int upper_bound_last_number = n - k + 1;
			if (upper_bound_last_number > R) upper_bound_last_number = R;
			for (int last_number = lower_bound_last_number; last_number <= upper_bound_last_number; last_number++)
			{
				int lower_n = n - last_number;
				int lower_k = k - 1;
				const vector<vector<int>>& lower_combs = results[lower_n][lower_k];
				int lower_comb_last_index = lower_k - 1;
				for (const vector<int>& lower_comb : lower_combs)
				{
					if (lower_comb[lower_comb_last_index] > last_number) break;
					vector<int> new_comb = lower_comb;
					new_comb.push_back(last_number);
					results[n][k].push_back(new_comb);
				}
			}
		}
	}
}

void unbag_formula(const vector<vector<vector<int>>>& bagged_formula, set<vector<int>>& unbagged_formula)
{
	for (const vector<vector<int>>& same_literal_count_group : bagged_formula)
	{
		for (const vector<int>& anded_clause : same_literal_count_group)
		{
			unbagged_formula.insert(anded_clause);
		}
	}
}

void join_vector_of_maps(const vector<map<string, string>>& vector_of_maps, map<string, string>& joined_map)
{
	for (const map<string, string>& vars_map_one_type : vector_of_maps) joined_map.insert(vars_map_one_type.begin(), vars_map_one_type.end());
}

bool map_inv_with_column_indices(const inv_t& inv, const vector<int>& column_indices, inv_t& new_inv)
{
	for (const vector<int>& anded_clause : inv)
	{
		vector<int> mapped_clause;
		for (int e : anded_clause)
		{
			if (column_indices[e] < 0) return false;
			mapped_clause.push_back(column_indices[e]);
		}
		std::sort(mapped_clause.begin(), mapped_clause.end());
		new_inv.insert(mapped_clause);
	}
	return true;
}

void merge_inv(const vector<inv_t>& invs, inv_t& merged_inv)
{
	assert(merged_inv.size() == 0);
	for (const inv_t& inv : invs)
	{
		for (const clause_t& clause : inv)
		{
			merged_inv.insert(clause);
		}
	}
}

void run_basic_methods_tests()
{
	// the following section tests function difference_two_sorted_vectors
	vector<int> result;
	difference_two_sorted_vectors({ 1,3,5 }, { 1,5 }, result);
	cout << (result == vector<int>({3})) << endl;
	result.clear();
	difference_two_sorted_vectors({ 1,2,10,35 }, { 10,35 }, result);
	cout << (result == vector<int>({ 1,2 })) << endl;
	result.clear();
	difference_two_sorted_vectors({ 7,10,12 }, { 7,10,12 }, result);
	cout << (result == vector<int>({})) << endl;
	result.clear();
	difference_two_sorted_vectors({ 7,10,12 }, {}, result);
	cout << (result == vector<int>({ 7,10,12 })) << endl;
	result.clear();
}

int binomialCoeff(int n, int k)
{
	assert(k <= MAX_COMB_K);
	// from https://www.geeksforgeeks.org/binomial-coefficient-dp-9/
	int C[MAX_COMB_K + 1];
	memset(C, 0, sizeof(C));

	C[0] = 1; // nC0 is 1

	for (int i = 1; i <= n; i++) {
		// Compute next row of pascal triangle using
		// the previous row
		for (int j = std::min(i, k); j > 0; j--)
			C[j] = C[j] + C[j - 1];
	}
	return C[k];
}


template<typename T>
void calc_combinations(const vector<T>& input_seq, int k, vector<vector<T>>& output_seq)
{
	// TODO-long-term: this can be accelerated
	assert(output_seq.size() == 0);
	int n = input_seq.size();
	if (n == 0 || n < k) return;
	assert(k <= MAX_COMB_K);
	if (k == 0) return;
	int output_len = binomialCoeff(n, k);
	output_seq.resize(output_len);
	for (int i = 0; i < output_len; i++) output_seq[i].resize(k);
	int indices[MAX_COMB_K + 1];
	for (int i = 0; i < k; i++) indices[i] = i;
	int comb_count = 0;
	bool next_comb_exists;
	// learned from Python implementation https://docs.python.org/3/library/itertools.html#itertools.combinations
	do
	{
		for (int i = 0; i < k; i++) output_seq[comb_count][i] = input_seq[indices[i]];
		comb_count++;
		next_comb_exists = false;
		int i;
		for (i = k - 1; i >= 0; i--)
		{
			if (indices[i] != i + n - k)
			{
				next_comb_exists = true;
				break;
			}
		}
		if (next_comb_exists)
		{
			indices[i] += 1;
			for (int j = i + 1; j < k; j++)
			{
				indices[j] = indices[j - 1] + 1;
			}
		}
	} while (next_comb_exists);
}

template <typename T>
void calc_permutations(const vector<T>& input_seq, int k, vector<vector<T>>& output_seq)
{
	vector<vector<T>> comb_seq;
	calc_combinations(input_seq, k, comb_seq);
	vector<int> k_permutation;
	vector<vector<int>> all_k_permutations;
	for (int i = 0; i < k; i++) k_permutation.push_back(i);
	do
	{
		all_k_permutations.push_back(k_permutation);
	} while (std::next_permutation(k_permutation.begin(), k_permutation.end()));
	for (const vector<T>& comb : comb_seq)
	{
		// const vector<T>& seq_to_perm = comb;
		for (const vector<int>& k_permutation : all_k_permutations)
		{
			vector<T> perm;
			for (int i = 0; i < k; i++)
			{
				perm.push_back(comb[k_permutation[i]]);
			}
			output_seq.push_back(perm);
		}
	}
}

template<typename T>
void calc_powerset(const vector<T>& input_seq, vector<vector<T>>& output_seq)
{
	assert(output_seq.size() == 0);
	int input_length = input_seq.size();
	for (int output_length = 1; output_length <= input_length; output_length++)
	{
		vector<vector<T>> buffer;
		calc_combinations(input_seq, output_length, buffer);
		output_seq.insert(output_seq.end(), buffer.begin(), buffer.end());
	}
}

// Cartesian product, from https://stackoverflow.com/questions/5279051/how-can-i-create-cartesian-product-of-vector-of-vectors/17050528#17050528
template<typename T>
vector<vector<T>> cart_product(const vector<vector<T>>& v) {
	vector<vector<T>> s = { {} };
	for (const auto& u : v) {
		vector<vector<T>> r;
		for (const auto& x : s) {
			for (const auto y : u) {
				r.push_back(x);
				r.back().push_back(y);
			}
		}
		s = move(r);
	}
	return s;
}

template void calc_combinations<string>(const vector<string>& input_seq, int k, vector<vector<string>>& output_seq);
template void calc_combinations<int>(const vector<int>& input_seq, int k, vector<vector<int>>& output_seq);
template void calc_combinations<vector<int>>(const vector<vector<int>>& input_seq, int k, vector<vector<vector<int>>>& output_seq);
template void calc_combinations<tuple<vars_t, qalter_t, inv_t>>(const vector<tuple<vars_t, qalter_t, inv_t>>& input_seq, int k, vector<vector<tuple<vars_t, qalter_t, inv_t>>>& output_seq);
template void calc_permutations<string>(const vector<string>& input_seq, int k, vector<vector<string>>& output_seq);
template void calc_permutations<int>(const vector<int>& input_seq, int k, vector<vector<int>>& output_seq);
template void calc_powerset(const vector<int>& input_seq, vector<vector<int>>& output_seq);
template vector<vector<map<string, string>>> cart_product(const vector<vector<map<string, string>>>& v);
template vector<vector<string>> cart_product(const vector<vector<string>>& v);
template vector<vector<bool>> cart_product(const vector<vector<bool>>& v);
template vector<vector<int>> cart_product(const vector<vector<int>>& v);
template vector<vector<vector<int>>> cart_product(const vector<vector<vector<int>>>& v);
template vector<vector<vector<vector<int>>>> cart_product(const vector<vector<vector<vector<int>>>>& v);
template vector<vector<inv_t>> cart_product(const vector<vector<inv_t>>& v);
