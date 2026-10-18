import subprocess, sys, time
limit = float(sys.argv[1])
t0 = time.time()
try:
    p = subprocess.run(sys.argv[2:], stdout=sys.stdout, stderr=subprocess.STDOUT, timeout=limit)
    rc = p.returncode
except subprocess.TimeoutExpired:
    rc = 124
sys.stderr.write(f'{time.time()-t0:.2f} {rc}')
