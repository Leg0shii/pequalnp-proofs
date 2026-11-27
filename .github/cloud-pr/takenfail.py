#!/usr/bin/env python3
"""preflight.sh looks for .github/cloud-pr/takenfail.py: run W6's .github/taken/takenfail.py with the same arguments"""
import os, runpy, sys
t = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "taken", "takenfail.py")
sys.argv = [t] + sys.argv[1:]
runpy.run_path(t, run_name="__main__")
