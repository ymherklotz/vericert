import csv
import os
import sys
import subprocess
import statistics

def write_result(dicts, name):
    with open(name, mode='w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=["name", "vericert", "list", "hyper", "bambu", "opt"]) 
        writer.writeheader()
        for k, v in dicts.items():
            writer.writerow(v)

def invert(dicts):
    dict_of_lists = {}
    for outer_key, inner_dict in dicts.items():
        for inner_key, value in inner_dict.items():
            if inner_key in dict_of_lists:
                dict_of_lists[inner_key].append(value)
            else:
                dict_of_lists[inner_key] = [value]
    return dict_of_lists

def main():
    if not os.path.isdir('synthesis-results'):
        subprocess.run(["tar", "xvf", "synthesis-results.tar.xz"])

    current_dir = os.getcwd()
    sresult_script = "/home/ymh/projects/vericert-pldi2024/scripts/synthesis-results.scm"
    results = {}

    for curr in [("vericert-original", "vericert"), ("vericert-list-scheduling", "list"), 
                 ("vericert-hyperblock", "hyper"), ("bambu-noopt", "bambu"), 
                 ("bambu-opt", "opt")]:
        pdir = "synthesis-results/" + curr[0]
        print("processing:", pdir)
        os.chdir(current_dir + "/" + pdir)
        res = subprocess.run([sresult_script, "."], capture_output=True)

        with open(current_dir + "/" + curr[0] + ".csv", "wb") as f:
            f.write(res.stdout)
        
        str_res = res.stdout.decode("utf-8").splitlines()

        results[curr[1]] = {}
        csv_reader = csv.DictReader(str_res)
        for row in csv_reader:
            results[curr[1]][row["name"]] = row

    os.chdir(current_dir)

    cycles = {}
    area = {}
    time = {}
    delay = {}

    for key, _ in results["vericert"].items():
        cycles[key] = {"name": key}
        area[key] = {"name": key}
        time[key] = {"name": key}
        delay[key] = {"name": key}
        for tool, value in results.items():
            cycles[key][tool] = value[key]["cycles"]
            area[key][tool] = value[key]["slice"]
            time[key][tool] = str(float(value[key]["delay"]) * float(value[key]["cycles"]))
            delay[key][tool] = value[key]["delay"]

    ic = invert(cycles)
    cycles["median"] = {}
    for i, _ in cycles["adi"].items():
        if i != "name":
            cycles["median"][i] = str(statistics.median(map(int, ic[i])))

    ic = invert(area)
    area["median"] = {}
    for i, _ in area["adi"].items():
        if i != "name":
            area["median"][i] = str(statistics.median(map(int, ic[i])))

    ic = invert(time)
    time["median"] = {}
    for i, _ in time["adi"].items():
        if i != "name":
            time["median"][i] = str(statistics.median(map(float, ic[i])))

    ic = invert(delay)
    delay["median"] = {}
    for i, _ in delay["adi"].items():
        if i != "name":
            delay["median"][i] = str(statistics.median(map(float, ic[i])))

    write_result(cycles, "cycles.csv")
    write_result(area, "area.csv")
    write_result(time, "speed.csv")
    write_result(delay, "delay.csv")

    subprocess.run(["gnuplot", "-p", "-e", 'set term svg size 1200,800 fixed; set output "bar-plot.svg"', "bar-plot.gp"])
    subprocess.run(["firefox", "bar-plot.svg"])

if __name__ == '__main__':
    main()
