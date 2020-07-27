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
        Print out BDD information about top element on stack

e
	Pop top two elements and compare for equality

s name
	Pop top stack element and store in named register.

r name
	Retrieve element from register and push onto top of stack

d name
        Delete named register
	
