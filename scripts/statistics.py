import datetime
import re
import subprocess
import sys
import urllib.request


def collect(d):
    try:
        n_admitted = len(subprocess.check_output(
            ["grep", "-r", "-E", "Admitted", d]).splitlines())
    except: n_admitted = 0

    try: n_theorems = len(subprocess.check_output(
            ["grep", "-r", "-E", "Theorem|Lemma|Remark", d]).splitlines())
    except: n_theorems = 0

    try: n_qed = len(subprocess.check_output(
            ["grep", "-r", "-E", "Qed|Defined", d]).splitlines())
    except: n_qed = 0

    try: n_files = len(subprocess.check_output(["find", d, "-name", "*.v"]).splitlines())
    except: n_files = 0

    try:
        ps = subprocess.Popen(["find", d, "-name", "*.v"], stdout=subprocess.PIPE)
        output = subprocess.check_output(["xargs", "wc"], stdin=ps.stdout).decode("utf-8").splitlines()[-1]
        ps.wait()
        n_lines = int(re.match("\s*(\d+)", output).group().strip())
    except: n_lines = 0

    return (n_files, n_lines, n_admitted, n_theorems, n_qed)


def pick_colour(n, m):
    if n > 0.2 * m: return "red"
    elif n > 0.1 * m: return "orange"
    elif n == 0: return "brightgreen"
    else: return "yellow"


def main(d):
    n_files, n_lines, n_admitted, n_theorems, n_qed = collect(d)
    colour = pick_colour(n_admitted, n_theorems)

    url = "https://img.shields.io/badge/admitted%20proofs-{}-{}?style=flat".format(
        str(n_admitted), colour)

    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with open("admitted.svg", "wb") as f:
        with urllib.request.urlopen(req) as r:
            f.write(r.read())

    with open(str(datetime.datetime.now()).replace(" ", "_")+".csv", "w") as f:
        f.write("n_files,n_lines,n_admitted,n_theorems,n_qed\n"
                +str(n_files)+","+str(n_lines)+","
                +str(n_admitted)+","+str(n_theorems)+","+str(n_qed)+"\n")


if __name__ == "__main__":
    main(sys.argv[1])
