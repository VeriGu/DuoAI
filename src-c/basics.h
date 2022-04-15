#ifndef BASICS_H
#define BASICS_H

#include <iostream>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <cstring>
#include <cassert>
#include <string>
#include <vector>
#include <numeric>
#include <algorithm>
#include <tuple>
#include <map>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <iterator>
#include <ctime>
#include <climits>
#include <chrono>
using std::cout; using std::endl; using std::ifstream; using std::ofstream;
using std::string; using std::vector; using std::pair; using std::tuple;
using std::stringstream;
using std::map; using std::unordered_set; using std::unordered_map; using std::set; using std::queue;
using std::reverse_iterator;

#define MAX_COMB_K 10
#define min2(x,y) (x<y? x:y)
#define max2(x,y) (x<y? y:x)
#define neg_p(p, num_predicates) (p < num_predicates? p + num_predicates: p - num_predicates)
#define time_now (std::chrono::steady_clock::now)
#define time_diff(x,y) ((int)std::chrono::duration_cast<std::chrono::microseconds>(x - y).count())
#define time_diff_in_seconds(x,y) ((int)std::chrono::duration_cast<std::chrono::seconds>(x - y).count())
#define not_implemented_exception(s) (std::runtime_error(string("Not implemented yet! ") + s))
#define startswith(s1,s2) (s1.rfind(s2, 0) == 0)

inline string vec_to_str(const vector<int>& vec)
{
	string output = "(";
	for (int e : vec) output += std::to_string(e) + ",";
	return output + ")";
}

inline string vec_to_str(const vector<bool>& vec)
{
	string output = "(";
	for (int e : vec) output += std::to_string(e) + ",";
	return output + ")";
}

inline string vec_to_str(const vector<string>& vec)
{
	string output = "(";
	for (const string& e : vec) output += e + ",";
	return output + ")";
}

typedef vector<int> vars_t;     // number of quantified variables for each type, consistent with type_order, e.g., [2, 1, 2]
typedef vector<int> lead_forall_vars_t;
typedef vector<int> inst_t;     // number of objects for each type in an instance, consistent with type_order, e.g., [2, 1, 2]
typedef vector<int> clause_t;   // an anded clause, consisting of column indices of predicates, e.g., [0, 3]
typedef set<vector<int>> inv_t;      // a candidate invariant in disjunctive normal form (DNF), represented by column indices of predicates, e.g., [[3, 4, 7], [2]]
typedef vector<bool> qalter_t;  // quantifier alternation, length = # of types, e.g., [false, true, false] -> forall exists forall
typedef vector<int> noncore_comb_t;  // a combination of noncore candidates

struct Config
{
	int max_literal, max_exists, max_ored_clauses, max_anded_literals, max_pos_exists;
	bool one_to_one_exists;
	struct one_to_one_triple
	{
		string func_name;
		int in_type, out_type;
	} one_to_one;
	map<int, string> total_ordered_types;  // from type_index to relation_name that defines the total order
	vector<string> type_order;  // used to contrain candidate invariants in EPR
	map<string, int> type_name_to_index;
	map<string, string> type_abbrs;
	vector<string> type_abbr_list;
	map<string, vector<int>> relations;
	map<string, pair<vector<int>, int>> functions;
	map<string, int> individuals;
	map<string, vector<string>> template_vars_map;  // key: type name (e.g., "node"), value: variable names (e.g., ["N1", "N2", "N3"])
	vector<inst_t> instance_sizes;  // e.g., [[2,1,2], [2,1,3], [2,2,2], [2,2,3], ...], consistent with type_order
	bool hard;
	vector<string> safety_properties;
	vector<pair<string, int>> checked_inv_pairs;
	map<string, vector<string>> shadow_relations;
};

struct DataMatrix
{
	int** data_ptr;
	int nrow;
	int ncol;
};

enum class Predicate_Type { bool_idv = 1, eq = 2, le = 3, relation_p = 4 };
enum class Term_Subtype { idv = 1, func = 2, qvar = 3 };

struct PredicateRep
{
	Predicate_Type predicate_type;  // 1: boolean individual, 2: equality, 3: le, 4: relation predicate
	string relation_name;  // individual name for Type 1, relation name for Type 4, empty string for Types (2)(3)
	int primary_type;  // type index for Types (2)(3), -1 for Types (1)(4)
	vector<Term_Subtype> term_subtypes;  // length = 0 for Type (1), 2 for Types (2)(3), relation_signature.size() for Type (4). 1: individual, 2: function application, 3: quantified variable
	vector<string> terms;  // individual name for Subtype (1), function name for Subtype (2), variable name suffix (type_abbr excluded) for Subtype (3)
	vector<vector<string>> functions_args;  // length = number of Subtype (2) terms, second length = argument list size for that function, final string: variable name suffix (type_abbr excluded) (assume no function application on individuals)
};

void join_string(const vector<string>& v, char c, string& s);
void join_string(const vector<string>& v, const string& c, string& s);
void split_string(const string& str, char delimeter, vector<string>& splitted_results);
void split_string(const string& str_, const string& delimeter, vector<string>& splitted_results);
void remove_matching_parenthesis(const string& input_string, string& output_string);
int** contiguous_2d_array(int nrow, int ncol);
void difference_two_sorted_vectors(const vector<int>& longer_vec, const vector<int>& shorter_vec, vector<int>& difference_vec);
void qalter_to_unique_ordered(const qalter_t& qalter, vector<bool>& is_unique_ordered);
void construct_vars_vector(const string& type_abbr, int vars_number, vector<string>& vars_vector);
void construct_vars_vector(const string& type_abbr, const vector<int>& var_indices, vector<string>& vars_vector);
void split_n_into_k_numbers_bulk(int N, int K, int R, vector<vector<vector<vector<int>>>>& results);
void unbag_formula(const vector<vector<vector<int>>>& bagged_formula, set<vector<int>>& unbagged_formula);
void join_vector_of_maps(const vector<map<string, string>>& vector_of_maps, map<string, string>& joined_map);
bool map_inv_with_column_indices(const inv_t& inv, const vector<int>& column_indices, inv_t& new_inv);
void merge_inv(const vector<inv_t>& invs, inv_t& merged_inv);
void run_basic_methods_tests();

// hash function for unordered_set<vector<int>>, from https://stackoverflow.com/questions/29855908/c-unordered-set-of-vectors/29855973#29855973
struct VectorHash {
	size_t operator()(const std::vector<int>& v) const {
		size_t seed = 0;
		for (int i : v) {
			seed ^= i + 0x9e3779b9 + (seed << 6) + (seed >> 2);
		}
		return seed;
	}
};

// a temporary hash function for unordered_set<vector<vector<int>>>, in fact the the order in the outer vector does not matter, may need to change
struct SetVectorHash {
	size_t operator()(const std::set<vector<int>>& v) const {
		size_t seed_sum = 0;
		for (const vector<int>& subv : v)
		{
			size_t seed = 0;
			for (int i : subv) {
				seed ^= i + 0x9e3779b9 + (seed << 6) + (seed >> 2);
			}
			seed_sum ^= seed + (seed << 5) + 0x5e673ad6;
		}
		return seed_sum;
	}
};

struct Vector3dHash {
	size_t operator()(const std::vector<vector<vector<int>>>& vec3d) const {
		size_t seed3d = 0;
		for (const vector<vector<int>>& vec2d : vec3d)
		{
			size_t seed2d = 0;
			for (const vector<int>& vec1d : vec2d)
			{
				size_t seed1d = 0;
				for (int i : vec1d) {
					seed1d ^= i + 0x9e3779b9 + (seed1d << 6) + (seed1d >> 2);
				}
				seed2d ^= seed1d + 0x5e673ad6 + (seed2d << 5) + (seed2d >> 1);
			}
			seed3d ^= seed2d + 0xaf87312d + (seed3d << 4) + (seed3d >> 2);
		}
		return seed3d;
	}
};

typedef unordered_set<inv_t, SetVectorHash> inv_set_t;  // an invariant set
typedef map<vars_t, map<qalter_t, inv_set_t>> invs_dict_t;  // an invariant dict

// auxiliary functions for string trimming, from https://www.techiedelight.com/trim-string-cpp-remove-leading-trailing-spaces/
const std::string WHITESPACE = " \n\r\t\f\v";
inline std::string ltrim(const std::string& s)
{
	size_t start = s.find_first_not_of(WHITESPACE);
	return (start == std::string::npos) ? "" : s.substr(start);
}
inline std::string rtrim(const std::string& s)
{
	size_t end = s.find_last_not_of(WHITESPACE);
	return (end == std::string::npos) ? "" : s.substr(0, end + 1);
}
inline std::string trim_string(const std::string& s)
{
	return rtrim(ltrim(s));
}

inline void insert_in_sorted_vector(vector<int>& sorted_vec, int element)
{
	auto it = std::upper_bound(sorted_vec.cbegin(), sorted_vec.cend(), element);
	sorted_vec.insert(it, element);
}

int binomialCoeff(int n, int k);

template <typename T>
void calc_combinations(const vector<T>& input_seq, int k, vector<vector<T>>& output_seq);
template <typename T>
void calc_permutations(const vector<T>& input_seq, int k, vector<vector<T>>& output_seq);
template <typename T>
void calc_powerset(const vector<T>& input_seq, vector<vector<T>>& output_seq);
template<typename T>
vector<vector<T>> cart_product(const vector<vector<T>>& v);

#endif
