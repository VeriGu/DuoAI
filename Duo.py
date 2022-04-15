import sys
import subprocess
import time
import os
import shutil
from threading import Thread
import atexit

MAX_TEMPLATE_INCREASE = 3
THREAD_CHECK_STATUS_INTERVAL = 0.1
INIT_TIMEOUT = 1200
TIMEOUT_FACTOR = 6

running_procs = []  # list of C++ processes running, kill them upon exit of this program

def template_increase_to_max_retry(curr_template_increase, is_forall_only):
    if is_forall_only:
        return max(curr_template_increase, 1)
    else:
        return max(curr_template_increase, 2)

class Duo:
    def __init__(self, PROBLEM):
        self.global_start_time = time.time()
        self.PROBLEM = PROBLEM
        simulation_file_path = 'auto_samplers/{}'.format(PROBLEM)
        shutil.rmtree(simulation_file_path, ignore_errors=True)
        if not os.path.exists(simulation_file_path):
            os.makedirs(simulation_file_path)
        if not os.path.exists('configs'):
            os.mkdir('configs')
        if not os.path.exists('src-c/runtime'):
            os.mkdir('src-c/runtime')
        c_runtime_path = 'src-c/runtime/' + PROBLEM
        shutil.rmtree(c_runtime_path, ignore_errors=True)
        os.mkdir(c_runtime_path)
        os.mkdir(c_runtime_path + '/bottom_up')
        os.mkdir(c_runtime_path + '/single_export')
        self.signal_passing_file = c_runtime_path + '/signals.txt'
        with open(self.signal_passing_file, 'w'):
            pass
        output_path = 'outputs/{}'.format(PROBLEM)
        shutil.rmtree(output_path, ignore_errors=True)
        os.makedirs(output_path)
        # these two are shared variables across threads, if simulation_starts = [True True False] and simulation_ends = [True False False], it means the simulation is running for the second time
        self.simulation_starts = [False for _ in range(MAX_TEMPLATE_INCREASE)]
        self.simulation_ends = [False for _ in range(MAX_TEMPLATE_INCREASE)]

    def translate_and_simulate_ivy_protocol(self, curr_template_increase):
        if curr_template_increase > 0:
            print('Re-simulate protocol with larger instances')
        if self.simulation_starts[curr_template_increase]:  # the other thread has started simulation
            wait_cycle = 0
            while not self.simulation_ends[curr_template_increase]:
                if wait_cycle == 0:
                    print('Waiting for simulation to finish in the other thread')
                time.sleep(THREAD_CHECK_STATUS_INTERVAL)
                wait_cycle += 1
        else:
            self.simulation_starts[curr_template_increase] = True
            subprocret = subprocess.run(
                ['python', 'translate.py', self.PROBLEM, '--template_increase={}'.format(curr_template_increase)],
                cwd='src-py/')
            if subprocret.returncode != 0:
                print(
                    'translate.py fails to parse and translate the input Ivy file. Please use $ivy_check PROTOCOL.ivy to '
                    'check if the Ivy file has the correct syntax and grammar. If it does, the problem may come from the '
                    'limitation of Duo, which does not support all Ivy features. Exiting...')
                os._exit(-1)
            num_process = len(os.listdir('auto_samplers/{}'.format(PROBLEM)))
            running_simulation_procs = []
            for proc_id in range(num_process):
                proc = subprocess.Popen(['python', '{}_{}.py'.format(self.PROBLEM, proc_id)], cwd='auto_samplers/{}'.format(PROBLEM))
                running_procs.append(proc)
                running_simulation_procs.append(proc)
            for proc in running_simulation_procs:
                proc.wait()
            self.simulation_ends[curr_template_increase] = True
            print('All simulation processes finished. Traces written to traces/{}/*.csv'.format(PROBLEM))

    def enumerate_and_refine_invariants(self, curr_template_increase, is_forall_only):
        success = False
        max_retry = template_increase_to_max_retry(curr_template_increase, is_forall_only)
        parallel_instance_str = 'forall_only' if is_forall_only else 'top_down_or_bottom_up'
        curr_timeout = INIT_TIMEOUT
        for init_attempt in range(max_retry + 1):
            proc = subprocess.Popen(['./main', self.PROBLEM, '--parallel_instance={}'.format(parallel_instance_str),
                                     '--template_increase={}'.format(curr_template_increase), '--init_attempt={}'.format(init_attempt)], cwd='src-c/')
            running_procs.append(proc)
            try:
                proc.wait(timeout=curr_timeout)
            except subprocess.TimeoutExpired:
                print('Enumeration and refinement timed out after {} seconds.'.format(curr_timeout))
                proc.kill()
            finally:
                with open(self.signal_passing_file, 'r') as infile:
                    for line in infile:
                        success = success or 'c' in line or 'm' in line or 't' in line or 'b' in line
                if success:
                    break
                curr_timeout *= TIMEOUT_FACTOR
        return success

    def cleanup_and_exit(self):
        total_time = time.time() - self.global_start_time
        kill_child_processes()
        print('Duo runtime: {:.3f}s'.format(total_time))
        os._exit(0)

    def run(self):
        for curr_template_increase in range(MAX_TEMPLATE_INCREASE):
            self.translate_and_simulate_ivy_protocol(curr_template_increase)
            if curr_template_increase == 0:
                forall_only_control_thread = Thread(target=self._forall_only_process)
                forall_only_control_thread.start()
            success = self.enumerate_and_refine_invariants(curr_template_increase, False)
            if success:
                break
        self.cleanup_and_exit()

    def _forall_only_process(self):
        for curr_template_increase in range(MAX_TEMPLATE_INCREASE):
            self.translate_and_simulate_ivy_protocol(curr_template_increase)
            success = self.enumerate_and_refine_invariants(curr_template_increase, True)
            if success:
                self.cleanup_and_exit()


def kill_child_processes():
    # reference: https://www.adamsmith.haus/python/examples/4871/subprocess-kill-all-subprocess-upon-exiting-the-script
    print('cleanup')
    for proc in running_procs:
        if proc.poll() is None:  # process has not terminated yet
            print('killing child process')
            proc.kill()


if __name__ == '__main__':
    atexit.register(kill_child_processes)
    assert len(sys.argv) >= 2
    PROBLEM = sys.argv[1]
    Duo_obj = Duo(PROBLEM)
    Duo_obj.run()
