#include "Solver.h"
#include "InvRefiner.h"
using namespace std::chrono_literals;

#define TIMEOUT 2s


bool auto_enumerate_and_refine_with_timeout(InvRefiner& refiner)
{
	return refiner.auto_enumerate_and_refine();
}

bool test_f(int a)
{
	return a > 3;
}

int main(int argc, char* argv[])
{
	if (!(argc >= 2)) {
		cout << "Please specify a protocol" << endl;
		exit(-1);
	}

	auto start_time = time_now();
	string problem = argv[1];

	int template_increase = 0;
	int max_retry = 1;
	Parallel_Instance parallel_instance = Parallel_Instance::forall_only;
	for (int i = 2; i < argc; i++) {
		string arg_str = argv[i];
		if (arg_str.rfind("--max_retry=", 0) == 0) {
			max_retry = atoi(arg_str.substr(12).c_str());
		}
		else if (arg_str.rfind("--parallel_instance=", 0) == 0) {
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
		else {
			cout << "Invalid command line argument " << arg_str << endl;
			exit(-1);
		}
	}
	
	bool success = false;
	int num_attempt = 0;
	while (!success && num_attempt <= max_retry)
	{
		auto retry_start_time = time_now();
		if (num_attempt > 0)
		{
			cout << "Retry with a larger formula size" << endl;
		}
		InvRefiner refiner(problem, parallel_instance, Refine_degree::removal_and_coimpl, template_increase, num_attempt);
		auto solver_constructed_time = time_now();
		cout << "Solver/Refiner constructor time: " << time_diff(solver_constructed_time, retry_start_time) << endl;
		// set timeout for a function call, reference: https://stackoverflow.com/a/56268886
		std::packaged_task<bool(InvRefiner&)> task(test_f);
		auto future = task.get_future();
		std::thread thr(std::move(task), 2);
		if (future.wait_for(TIMEOUT) != std::future_status::timeout)
		{
			thr.join();
			success = future.get(); 
		}
		else
		{
			thr.detach(); 
			throw std::runtime_error("Timeout");
		}
		num_attempt++;
	}
	
	auto end_time = time_now();

	cout << "C++ main runtime: " << time_diff(end_time, start_time) << endl;

	return 0;
}
