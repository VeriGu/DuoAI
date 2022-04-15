#include "preprocessing.h"

void read_config(const string& config_file, Config* config)
{
	ifstream in(config_file.c_str());
	if (!in)
	{
		cout << "Can't open config file " << config_file << endl;
		exit(-1);
	}
	config->max_literal = 0;
	config->one_to_one_exists = false;
	string line;
	while (getline(in, line)) 
	{	
		if (line[0] == '#') continue;  // comment line
		else if (startswith(line, "one-to-one:"))  // equivalent as line.startswith("one-to-one") in Python
		{
			vector<string> one_to_one_strings;
			assert(!config->one_to_one_exists);
			config->one_to_one_exists = true;
			split_string(line.substr(11), ',', one_to_one_strings);
			assert(one_to_one_strings.size() == 3);
			config->one_to_one.func_name = one_to_one_strings[0];
			assert(config->type_name_to_index.find(one_to_one_strings[1]) != config->type_name_to_index.end() && config->type_name_to_index.find(one_to_one_strings[2]) != config->type_name_to_index.end());
			config->one_to_one.in_type = config->type_name_to_index.at(one_to_one_strings[1]);
			config->one_to_one.out_type = config->type_name_to_index.at(one_to_one_strings[2]);
			if (config->one_to_one.out_type != config->one_to_one.in_type + 1)
			{
				cout << "Error! Two bijection-related sorts " << one_to_one_strings[1] << " and " << one_to_one_strings[2] << " must be adjacent and in order in the Ivy sort declaration" << endl;
				exit(-1);
			}
			if (config->total_ordered_types.find(config->one_to_one.in_type) != config->total_ordered_types.end()) config->total_ordered_types[config->one_to_one.out_type] = "";
			else if(config->total_ordered_types.find(config->one_to_one.out_type) != config->total_ordered_types.end()) config->total_ordered_types[config->one_to_one.in_type] = "";
		}
		else if (startswith(line, "total-ordered-types:"))
		{
			assert(config->total_ordered_types.size() == 0);
			assert(config->type_order.size() > 0);
			vector<vector<string>> groups;
			two_delimeters_parse_line(line.substr(20), ';', ':', groups);
			for (const vector<string>& group : groups)
			{
				assert(group.size() == 2);
				const string& type_name = group[0];
				const string& relation_name = group[1];
				config->total_ordered_types[config->type_name_to_index.at(type_name)] = relation_name;
			}
		}
		else if (startswith(line, "template:"))
		{
			assert(config->type_order.size() == 0);
			assert(config->type_name_to_index.size() == 0);
			vector<vector<string>> groups;
			two_delimeters_parse_line(line.substr(10), ';', ':', groups);
			int type_index = 0;
			for (const vector<string>& group : groups)
			{
				const string& type_name = group[0];
				config->type_order.push_back(type_name);
				config->type_name_to_index[type_name] = type_index;
				vector<string> var_names;
				split_string(group[1], ',', var_names);
				config->template_vars_map[type_name] = var_names;
				type_index++;
			}
		}
		else if (startswith(line, "relations:"))
		{
			assert(config->relations.size() == 0);
			vector<vector<string>> groups;
			two_delimeters_parse_line(line.substr(10), ';', ':', groups);
			for (const vector<string>& group : groups)
			{
				const string& relation_name = group[0];
				vector<string> relation_signature;
				split_string(group[1], ',', relation_signature);
				for (const string& arg_type : relation_signature)
				{
					config->relations[relation_name].push_back(config->type_name_to_index.at(arg_type));
				}
			}
		}
		else if (startswith(line, "functions:"))
		{
			assert(config->functions.size() == 0);
			vector<vector<string>> groups;
			two_delimeters_parse_line(line.substr(10), ';', ':', groups);
			for (const vector<string>& group : groups)
			{
				const string& function_name = group[0];
				vector<string> function_signature;
				split_string(group[1], ',', function_signature);
				int output_type = config->type_name_to_index.at(function_signature.back());
				function_signature.pop_back();
				vector<int> args_type;
				for (const string& arg_type : function_signature)
				{
					args_type.push_back(config->type_name_to_index.at(arg_type));
				}
				config->functions[function_name] = std::make_pair(args_type, output_type);
			}
		}
		else if (startswith(line, "individuals:"))
		{
			assert(config->individuals.size() == 0);
			vector<vector<string>> groups;
			two_delimeters_parse_line(line.substr(12), ';', ':', groups);
			for (const vector<string>& group : groups)
			{
				const string& individual_name = group[0];
				const string& individual_type_name = group[1];
				int individual_type = individual_type_name == "bool" ? BOOL_INDIVIDUAL_TYPE : config->type_name_to_index.at(group[1]);
				config->individuals[individual_name] = individual_type;
			}
		}
		else if (startswith(line, "type-abbr:"))
		{
			assert(config->type_abbrs.size() == 0);
			vector<vector<string>> type_abbr_as_strings;
			two_delimeters_parse_line(line.substr(10), ';', ':', type_abbr_as_strings);
			for (const vector<string>& one_type_abbr_pair : type_abbr_as_strings)
			{
				assert(one_type_abbr_pair.size() == 2);
				config->type_abbrs[one_type_abbr_pair[0]] = one_type_abbr_pair[1];
			}
		}
		else if (startswith(line, "instance-sizes:"))
		{
			assert(config->instance_sizes.size() == 0);
			vector<vector<string>> instances_sizes_as_strings;
			two_delimeters_parse_line(line.substr(15), ';', ',', instances_sizes_as_strings);
			for (const vector<string>& one_instance_size_as_string : instances_sizes_as_strings)
			{
				vector<int> one_instance_size;
				for (const string& number : one_instance_size_as_string)
				{
					one_instance_size.push_back(stoi(number));
				}
				config->instance_sizes.push_back(one_instance_size);
			}
		}
		else if (startswith(line, "max-literal:"))
		{
			assert(config->max_literal == 0);
			int max_literal = std::stoi(line.substr(12));
			config->max_literal = max_literal;
		}
		else if (startswith(line, "max-exists:"))
		{
			assert(config->max_exists == 0);
			int max_exists = std::stoi(line.substr(11));
			config->max_exists = max_exists;
		}
		else if (startswith(line, "max-pos-exists:"))
		{
			assert(config->max_pos_exists == 0);
			int max_pos_exists = std::stoi(line.substr(15));
			config->max_pos_exists = max_pos_exists;
		}
		else if (startswith(line, "max-or:"))
		{
			assert(config->max_ored_clauses == 0);
			int max_ored_clauses = std::stoi(line.substr(7));
			config->max_ored_clauses = max_ored_clauses;
		}
		else if (startswith(line, "max-and:"))
		{
			assert(config->max_anded_literals == 0);
			int max_anded_literals = std::stoi(line.substr(8));
			config->max_anded_literals = max_anded_literals;
		}
		else if (startswith(line, "hard: true"))
		{
			config->hard = true;
		}
		else if (startswith(line, "safety-property:"))
		{
			if (config->hard)
			{
				config->safety_properties.push_back(line.substr(16));
			}
		}
		else if (line.rfind("checked-inv:", 0) == 0)
		{
			vector<string> checked_inv_pair;
			split_string(line.substr(12), ',', checked_inv_pair);
			assert(checked_inv_pair.size() == 2);
			const string& relation_name = checked_inv_pair[0];
			int partial_func_index = std::stoi(checked_inv_pair[1]);
			config->checked_inv_pairs.push_back({ relation_name, partial_func_index });
		}
		else if (startswith(line, "shadow-relations:"))
		{
			vector<vector<string>> shadow_relations_as_strings;
			two_delimeters_parse_line(line.substr(17), ';', ',', shadow_relations_as_strings);
			for (const vector<string>& shadow_relation : shadow_relations_as_strings)
			{
				assert(shadow_relation.size() >= 2);
				config->shadow_relations[shadow_relation[0]] = { shadow_relation.begin() + 1, shadow_relation.end() };
			}
		}
		else
		{
			cout << "Unparsable line in config" << line << endl;
		}
	}
	for (const string& type_name : config->type_order) config->type_abbr_list.push_back(config->type_abbrs.at(type_name));
}

void read_trace(const string& csv_file, vector<string>& full_predicates, DataMatrix& init_data_mat)
{
	// read the sample file, outputs the predicates (i.e., first line of csv file) and the 0/1 sample matrix
	assert(full_predicates.size() == 0);
	assert(init_data_mat.data_ptr == NULL);
	char* file_read_buffer = new char[FILE_BUFFER_SIZE];
	FILE* fp = fopen(csv_file.c_str(), "r");
	size_t newLen = 0;
	if (fp != NULL) {
		newLen = fread(file_read_buffer, sizeof(char), FILE_BUFFER_SIZE, fp);
		if (newLen >= FILE_BUFFER_SIZE - 1) {
			delete[] file_read_buffer;
			file_read_buffer = new char[16 * FILE_BUFFER_SIZE];
			fclose(fp);
			fp = fopen(csv_file.c_str(), "r");
			newLen = fread(file_read_buffer, sizeof(char), 16 * FILE_BUFFER_SIZE, fp);
		}
		if (newLen >= 16 * FILE_BUFFER_SIZE - 1) {   // if still fails, return
			cout << "Trace file exceeds input buffer size. You can increase FILE_BUFFER_SIZE at the beginning of preprocessig.h" << endl;
			cout << "But in fact, our tool has effectively failed. The huge trace file will stall the invariant learner or exhausts memory during enumeration" << endl;
			exit(-1);
		}
		if (ferror(fp) != 0) {
			fputs("Error reading file", stderr);
		}
		fclose(fp);
	}
	else {
		cout << "Cannot open trace file " << csv_file << endl;
		exit(-1);
	}

	int landmark;
	for (int i = 0;; i++)
	{
		if (file_read_buffer[i] == '\n')
		{
			landmark = i;
			break;
		}
	}
	int newline_c = 1;
	if (file_read_buffer[landmark - 1] == '\r') newline_c = 2;
	string line(file_read_buffer, landmark);
	vector<string> before_merging;
	split_string(line, ',', before_merging); 
	merge_quoted_comma(before_merging, full_predicates);
	int ncol = full_predicates.size();
	vector<int> temp_data;
	int nchar_per_row = 2 * ncol + newline_c - 1;
	landmark++;
	assert((newLen - landmark) % nchar_per_row == 0);
	int nrow = (newLen - landmark) / nchar_per_row;
	assert(ncol > 0);
	if (nrow == 0)
	{
		// cout << "Warning! Trace file " << csv_file << " has zero samples." << endl;
	}
	for (int row = 0; row < nrow; row++)
	{
		int end = landmark + 2 * ncol;
		for (int i = landmark; i < end; i += 2)
		{
			if (file_read_buffer[i] == '1') temp_data.push_back(1);
			else
			{
				assert(file_read_buffer[i] == '0');
				temp_data.push_back(0);
			}
		}
		landmark += nchar_per_row;
	}
	assert(temp_data.size() % ncol == 0);
	assert(nrow == int(temp_data.size() / ncol));
	init_data_mat.data_ptr = contiguous_2d_array(nrow, ncol);
	std::copy(temp_data.begin(), temp_data.end(), init_data_mat.data_ptr[0]);
	init_data_mat.nrow = nrow;
	init_data_mat.ncol = ncol;
	delete[] file_read_buffer;
}

void add_negation(DataMatrix& data_mat)
{
	int nrow = data_mat.nrow, ncol = data_mat.ncol;
	int** old_data_ptr = data_mat.data_ptr;
	int** new_data_ptr = contiguous_2d_array(nrow, 2 * ncol);
	for (int i = 0; i < nrow; i++)
	{
		for (int j = 0; j < ncol; j++)
		{
			new_data_ptr[i][j] = old_data_ptr[i][j];
			new_data_ptr[i][j + ncol] = 1 - old_data_ptr[i][j];
		}
	}
	data_mat.ncol = 2 * ncol;
	data_mat.data_ptr = new_data_ptr;
	// warning: currently no memory free (delete []) for old_data_ptr
}

void two_delimeters_parse_line(const string& line, char top_delimeter, char secondary_delimeter, vector<vector<string>>& parsed_results)
{
	vector<string> segments;
	split_string(line, top_delimeter, segments);
	for (string segment : segments)
	{
		vector<string> segment_parsed_result;
		split_string(segment, secondary_delimeter, segment_parsed_result);
		if (segment_parsed_result.size() > 0)
		{
			parsed_results.push_back(segment_parsed_result);
		}
	}
}

void merge_quoted_comma(const vector<string>& before_merging, vector<string>& after_merging)
{
	// "p(X, Y)" in csv header will be split into "p(X) and Y)", so we need to merge them
	// assume "" matches otherwise may have bugs
	assert(after_merging.size() == 0);
	bool continuation = false;
	string temp;
	for (const string& str : before_merging)
	{
		if (continuation)
		{
			if (str.back() == '\"')
			{
				temp = temp + "," + str.substr(0, str.size() - 1);
				after_merging.push_back(temp);
				continuation = false;
				temp.clear();
			}
			else
			{
				temp = temp + "," + str;
			}
		}
		else
		{
			if (str[0] != '\"')
			{
				after_merging.push_back(str);
			}
			else
			{
				temp = str.substr(1);
				assert((temp.size() > 0) && (temp.back() != '\"'));
				continuation = true;
			}
		}
	}
}
