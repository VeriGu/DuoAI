#include "Solver.h"
#include "InvRefiner.h"


int main(int argc, char* argv[])
{
	if (!(argc >= 2)) {
		cout << "Please specify a protocol" << endl;
		exit(-1);
	}

	auto start_time = time_now();
	string problem = argv[1];

	int template_increase = 0;
	int init_attempt = 0;
	Parallel_Instance parallel_instance = Parallel_Instance::forall_only;
	for (int i = 2; i < argc; i++) {
		string arg_str = argv[i];
		if (arg_str.rfind("--parallel_instance=", 0) == 0) {
			string parallel_instance_str = arg_str.substr(20);
			if (parallel_instance_str == "forall_only") parallel_instance = Parallel_Instance::forall_only;
			else if (parallel_instance_str == "top_down") parallel_instance = Parallel_Instance::top_down;
			else if (parallel_instance_str == "bottom_up") parallel_instance = Parallel_Instance::bottom_up;
			else if (parallel_instance_str == "top_down_or_bottom_up") parallel_instance = Parallel_Instance::top_down_or_bottom_up;
			else
			{
				cout << "Invalid parallel_instance! Choose from forall_only, top_down, bottom_up, and top_down_or_bottom_up." << endl;
				exit(-1);
			}
		}
		else if (arg_str.rfind("--template_increase=", 0) == 0) {
			template_increase = atoi(arg_str.substr(20).c_str());
		}
		else if (arg_str.rfind("--init_attempt=", 0) == 0) {
			init_attempt = atoi(arg_str.substr(15).c_str());
		}
		else {
			cout << "Invalid command line argument " << arg_str << endl;
			exit(-1);
		}
	}
	
	int num_attempt = init_attempt;
	if (num_attempt > 0)
	{
		cout << "Retry with a larger formula size" << endl;
	}

	InvRefiner refiner(problem, parallel_instance, Refine_degree::removal_and_coimpl, template_increase, num_attempt);
	refiner.auto_enumerate_and_refine();
	
	auto end_time = time_now();
	cout << "C++ main runtime: " << time_diff_in_seconds(end_time, start_time) << " seconds" << endl;
	return(0);
}
