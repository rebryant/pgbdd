Syntax for schedule interpreter.

Based on stack language

# ...
        Comment line

c C_1 C_2 ... C_k
        Retrieve specified clauses and push onto stack

a K
        Pop K+1 elements.  And them together and push result onto stack

q V_1 V_2 ... V_k
        Existentially quantify top stack element by specified variables and replace

i Docstring
        Print out BDD information about top element on stack.
	Docstring is appended to information.

s Name
        Store top stack element by Name.  Do not remove from stack

r Name
        Retrieved named element and push onto stack

= C T_1 T_2 ... T_k
    	Pop top of stack.  Prove that it implies equation
	with specified terms and constant C.
	Each T of form A.V where A is integer coefficient (possibly
	negative) and V is variable ID.  Variables should be in ascending order

>= C T_1 T_2 ... T_k
    	Pop top of stack.  Prove that it implies constraint
	with specified terms and constant C.
	Each T of form A.V where A is integer coefficient (possibly
	negative) and V is variable ID.  Variables should be in ascending order

