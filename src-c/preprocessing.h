#ifndef PREPROCESSING_H
#define PREPROCESSING_H

#include "basics.h"

#define FILE_BUFFER_SIZE (1 << 24)
#define BOOL_INDIVIDUAL_TYPE 224


void read_config(const string& config_file, Config* config);
void read_trace(const string& csv_file, vector<string>& predicates, DataMatrix& init_data_mat);
void add_negation(DataMatrix& data_mat);
void two_delimeters_parse_line(const string& line, char top_delimeter, char secondary_delimeter, vector<vector<string>>& parsed_results);
void merge_quoted_comma(const vector<string>& before_merging, vector<string>& after_merging);

#endif
