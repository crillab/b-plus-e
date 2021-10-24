**B+E** is built upon glucose 3.0 (MIT Licence).

# How to compile

```bash
cd core
make
```


# How to use


Please use the help to get information about the way of running it.

```bash
./BiPe --help-verbose
```


It is also possible to force some variables to be in the input or the output set specifically.
To do it you need to specify in the input file which variables are incriminated.
To specify input variables **{1,2}** you need to add the comment line **c i 1 2 0** in your input file.
To specify output variables **{2,3}** you need to add the comment line **c o 2 3 0** in your input file.
It is also possible to mix both input and output variables. Here is an example:

```bash
$ cat forceOutput.cnf
p cnf 6 7
c o 2 5 6 0
5 6 0
-1 -2 3 0
1 -3 0
2 -3 0
-1 -2 4 0
1 -4 0
2 -4 0
```


Forcing output variables is required when using **B+E** for projected model counting.

**Warning:** Using gates detection is incompatible with considering output var.
