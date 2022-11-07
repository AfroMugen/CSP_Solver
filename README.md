# CSP_Solver

csp_solver.py is expected to take in a CSP problem file and a flag to toggle forward checking. i.e.

`python csp_solver.py [problem_filename] [use_forward_check_flag]'
  
An example input would look like:

`python .\csp_solver.py .\problem_files\problem_file_1.txt 1`
  
Problem files are always of the same format:

-List of domains consisting of a sequence of colon separated integers.
  
-Every line after is a constraint of the format:
  
  -Integer * Variable + Integer Rel Variable/Integer
    
  -Rel is a comparison operator (==, !==, <=, >=, etc.)
    
  -Variables are always of the form "Xi" where i is a non-negative integer
    
There are example files within the problem_files folder.
