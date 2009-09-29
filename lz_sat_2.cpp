#include <vector>
#include <queue>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>
#include <assert.h>

#include <sys/time.h>
#include <sys/resource.h>

using namespace std;

//======================================================================
double get_cpu_time()
{
    double res;
    struct rusage usage;

    getrusage(RUSAGE_SELF, &usage);

    res = usage.ru_utime.tv_usec + usage.ru_stime.tv_usec;
    res *= 1e-6;
    res += usage.ru_utime.tv_sec + usage.ru_stime.tv_sec; 
	
    return res;
}

void get_line(ifstream &fs, vector<char> &buf)
{
    buf.clear();
    buf.reserve(4096);
    while(!fs.eof()) {
        char ch = fs.get();
        if(ch == '\n' || ch == '\377')
	    break;
        if(ch == '\r') 
	    continue;
        buf.push_back(ch);
    }
    buf.push_back('\0');
    return;
}

int get_token (char * & lp, char * token)
{
    char * wp = token;
    while (*lp && ((*lp == ' ') || (*lp == '\t'))) {
	lp++;
    }
    while (*lp && (*lp != ' ') && (*lp != '\t') && (*lp != '\n')) {
	*(wp++) = *(lp++);
    }
    *wp = '\0';                                 // terminate string
    return wp - token; 
}
//======================================================================

typedef unsigned CLiteral;

#define UNKNOWN 	2

#define VID(lit)	(lit>>1 )
#define SIGN(lit)	(lit & 1)

enum EDeductionStatus 
{
    CONFLICT = 100,
    NO_CONFLICT
};

enum ESolvingStatus
{
    SATISFIABLE = 500,
    UNSATISFIABLE,
    TIME_OUT
};

struct CClause 
{
    vector<CLiteral> literals;	//literal array, i.e. all the literals in this clause
    unsigned num_0;		//number of value 0 literals
    unsigned num_1;		//number of value 1 literals
};

struct CVariable
{
    unsigned	value;		//could be 0 (false), 1 (true) or UNKNOWN (unassigned)
    int		dlevel;		//decision level
    int 	antecedent;
    bool	marked;
    vector<unsigned> cl_idx[2];	//the clauses that this variable appears
};

struct CImplication
{
    CLiteral	lit;
    int		antecedent;
};

class CSolver
{
public:
    double		time_limit;
    unsigned		num_decisions;
    unsigned		num_conflicts;
    unsigned		num_implications;

private:
    double		init_time;
    unsigned		init_num_clauses;
    
    int			dlevel;		//current decision level
    vector<CClause> 	clauses;	//all the clauses
    vector<CVariable> 	variables;	//all the variables, index 0 is not used		
    vector<vector<CLiteral> > assign_stack;	//variables assigned at decision level n

    queue<CImplication>	implication_queue;	
    vector<int> 	conflicts;

    void verify_integrity(void);
private:
    unsigned literal_value(CLiteral lit) {	//it will return 0, 1 or something else (but may not be UNKNOWN)
	unsigned vid = VID(lit);
	unsigned sign = SIGN(lit);
	return (sign ^ variables[vid].value); 
    }

    bool time_out(void)	{
	return (get_cpu_time() - init_time > time_limit);
    }

    void set_var_value (int vid, int value);
    void unset_var_value (int vid);

    void init_solve(void);
    int preprocess(void);
    bool decide_next_branch(void);
    int deduce	(void);
    int analyze_conflicts(void);
    void backtrack(int dlevel);

public:
    int add_clause( vector<CLiteral> & lits);
    void set_var_number(int n);

    void read_cnf (char * filename);
    int solve (void);
    void print_solution(ostream & o = cout);
};

void CSolver::verify_integrity(void)
{
    for (unsigned i=0; i< clauses.size(); ++i) {
	unsigned n0 = 0, n1 = 0;
	CClause & cl = clauses[i];
	for (unsigned j=0; j< cl.literals.size(); ++j) {
	    if (literal_value(cl.literals[j]) == 0)
		++ n0;
	    else if (literal_value(cl.literals[j]) == 1)
		++ n1;
	}
	assert (n0 == cl.num_0 && n1 == cl.num_1);
    }
    for (unsigned i=1; i< variables.size(); ++i) {
	if (variables[i].value != UNKNOWN) {
	    if (variables[i].antecedent == -1) {
		assert (variables[i].dlevel == 0 ||
			VID(assign_stack[variables[i].dlevel][0]) == i);
	    }
	    else {
		CClause & cl = clauses[variables[i].antecedent];
		int dl = 0;
		for (unsigned j=0; j< cl.literals.size(); ++j) {	
		    CLiteral lit = cl.literals[j];
		    if (VID(lit) == i)
			continue;
		    else {
			assert (literal_value(lit) == 0);
			if (dl < variables[VID(lit)].dlevel)
			    dl = variables[VID(lit)].dlevel;
		    }
		}
		assert (dl == variables[i].dlevel);
	    }
	}
    }
}

void CSolver::set_var_number(int n)
{
    variables.resize( n + 1);
    for (unsigned i=0; i< variables.size(); ++i) {
	variables[i].value = UNKNOWN;
	variables[i].dlevel = -1;
	variables[i].marked = false;
    }
}

int CSolver::add_clause (vector<CLiteral> & lits) 
{
    int cl_id = clauses.size();
    clauses.resize( cl_id + 1);

    clauses[cl_id].num_0 = 0;
    clauses[cl_id].num_1 = 0;

    for (unsigned i=0; i< lits.size(); ++i) {
	int lit = lits[i];
	int vid = VID(lit);
	int sign = SIGN(lit);
	int l_value = literal_value (lit);

	clauses[cl_id].literals.push_back(lit);
	variables[vid].cl_idx[sign].push_back(cl_id);

	if (l_value == 0)
	    ++ clauses[cl_id].num_0 ;
	else if (l_value == 1)
	    ++ clauses[cl_id].num_1 ;
    }
    return cl_id;
}

bool CSolver::decide_next_branch(void)
{
    assert (implication_queue.empty());
    ++ num_decisions;

    ++ dlevel;

    int svar = 0;
    for (unsigned i=1; i< variables.size(); ++i) {
	if (variables[i].value == UNKNOWN) {
	    int phase = (random() & 1);
	    svar = i + i + phase;
	    break;
	}
    }

    if (svar != 0) {
	CImplication imp;
	imp.lit = svar;
	imp.antecedent = -1;
	implication_queue.push(imp);
	return true;
    }
    return false;
}

void CSolver::init_solve(void)
{
    init_num_clauses 	= clauses.size();
    init_time	 	= get_cpu_time();
    num_decisions	= 0;
    num_conflicts	= 0;
    num_implications	= 0;

    assign_stack.resize(variables.size());
    dlevel = 0;
}


int CSolver::preprocess (void)
{
    for (unsigned i=0; i< clauses.size(); ++i) {
	assert (clauses[i].literals.size() > 0);
	if (clauses[i].literals.size() == 1) {
	    CImplication imp;
	    imp.lit = clauses[i].literals[0];
	    imp.antecedent = -1;
	    implication_queue.push(imp);
	}
    }
    return deduce();
}

int CSolver::analyze_conflicts(void)
{
    assert (conflicts.size() > 0) ;
    CClause & conf_cl = clauses[conflicts[0]];
    conflicts.clear();
    ++ num_conflicts;

    if (dlevel == 0)	//current dlevel is 0, so unsatisfiable
	return 0;
    
    vector<CLiteral> learned_clause;
    int num_marked_current_dl = 0;

    for (unsigned i=0; i< conf_cl.literals.size(); ++i) {
	CLiteral lit = conf_cl.literals[i];
	assert (literal_value (lit) == 0);
	variables[VID(lit)].marked = true;	

	if (variables[VID(lit)].dlevel != dlevel)
	    learned_clause.push_back(lit);
	else 
	    ++ num_marked_current_dl;
    }
    assert (num_marked_current_dl > 1);

    vector<CLiteral> & assign_last_dl = assign_stack[dlevel];

    int i;
    for (i=assign_last_dl.size() - 1; i >= 0; --i) {
	CLiteral lit = assign_last_dl[i];
	if (variables[VID(lit)].marked == false) //it's not involved
	    continue;

	if (num_marked_current_dl == 1) {
	    learned_clause.push_back(lit^1);
	    break;
	}

	CClause & ante_cl = clauses[variables[VID(lit)].antecedent];
	for (unsigned j=0; j< ante_cl.literals.size(); ++j) {
	    CLiteral l = ante_cl.literals[j];
	    if (l == lit) //the implied variable
		continue;
	    //not the lit
	    assert (literal_value (l) == 0);
	    if (variables[VID(l)].marked != true) {
		variables[VID(l)].marked = true;
		if (variables[VID(l)].dlevel != dlevel)
		    learned_clause.push_back(l);
		else 
		    ++ num_marked_current_dl;
	    }
	}
	variables[VID(lit)].marked = false;
	-- num_marked_current_dl;
    }
    assert (i >= 0);

    int assert_lit = learned_clause.back();
    int assert_level = 0;
    assert (literal_value(assert_lit) == 0);
    variables[VID(assert_lit)].marked = false;

    for (unsigned i = 0; i < learned_clause.size() - 1; ++i) {
	int lit = learned_clause[i];
	assert (literal_value(lit) == 0);

	CVariable & var = variables[VID(lit)];
	assert (var.marked == true);
	var.marked = false;
	if (var.dlevel > assert_level)
	    assert_level = var.dlevel;
    }

    int cl_id = add_clause(learned_clause);
    CImplication imp;
    imp.lit = assert_lit;
    imp.antecedent = cl_id;
    implication_queue.push(imp);

    assert (assert_level < dlevel);
    return assert_level + 1;
}

void CSolver::set_var_value(int vid, int value)
{
    assert (value == 0 || value == 1);
    ++ num_implications;

    CVariable & var = variables[vid];
    var.value = value;

    vector<unsigned> & pos_clauses = var.cl_idx [1 - value];
    for (unsigned i=0; i< pos_clauses.size(); ++i) {
	CClause & cl = clauses[pos_clauses[i]];
	++ cl.num_1;
    }

    vector<unsigned> & neg_clauses = var.cl_idx[value];
    for (unsigned i=0; i< neg_clauses.size(); ++i) {
	int cl_id = neg_clauses[i];
	CClause & cl = clauses[cl_id];
	++ cl.num_0;
	if (cl.num_0 == cl.literals.size())
	    conflicts.push_back(neg_clauses[i]);
	else if (cl.num_0 == cl.literals.size() - 1 &&
		 cl.num_1 == 0) {
	    unsigned j;
	    for (j=0; j< cl.literals.size(); ++j) {
		CLiteral lit = cl.literals[j];
		if (variables[VID(lit)].value == UNKNOWN) {
		    CImplication imp;
		    imp.lit = lit;
		    imp.antecedent = cl_id;
		    implication_queue.push(imp);
		    break;
		}
	    }
	    assert (j < cl.literals.size());
	}
    }
}

void CSolver::unset_var_value(int vid)
{
    int value = variables[vid].value;
    assert (value != UNKNOWN);

    CVariable & var = variables[vid];

    vector<unsigned> & pos_clauses = var.cl_idx [1 - value];
    for (unsigned i=0; i< pos_clauses.size(); ++i) {
	CClause & cl = clauses[pos_clauses[i]];
	-- cl.num_1;
    }

    vector<unsigned> & neg_clauses = var.cl_idx[value];
    for (unsigned i=0; i< neg_clauses.size(); ++i) {
	CClause & cl = clauses[neg_clauses[i]];
	-- cl.num_0;
    }
    
    var.value = UNKNOWN;
}

void CSolver::backtrack(int back_dl)
{
    assert (back_dl <= dlevel);
    for (int i=dlevel; i >= back_dl; --i) {
	vector<CLiteral> & assigned_at_dlevel = assign_stack[i];
	for (unsigned j=0; j< assigned_at_dlevel.size(); ++j) {
	    int vid = VID(assigned_at_dlevel[j]);
	    unset_var_value(vid);
	    variables[vid].dlevel = -1;
	}
	assigned_at_dlevel.clear();
    }
    dlevel = back_dl - 1;
}

int CSolver::deduce(void)
{
    while (!implication_queue.empty() && conflicts.size()==0) {
	CLiteral lit = implication_queue.front().lit;
	int ante = implication_queue.front().antecedent;

	int vid = VID(lit);
	implication_queue.pop();
	
	CVariable & var = variables[vid];
	if ( var.value == UNKNOWN) { // an implication
	    assert (var.dlevel == -1);

	    set_var_value(vid, 1 - SIGN(lit));

	    var.dlevel = dlevel;
	    var.antecedent = ante;
	    assign_stack[dlevel].push_back(lit);
	}
    }
    //if loop exited because of a conflict, we need to clean implication queue
    while(!implication_queue.empty()) 
	implication_queue.pop();

    return (conflicts.size()?CONFLICT:NO_CONFLICT);
}

int CSolver::solve(void)
{
    init_solve();

    if(preprocess()==CONFLICT) 
	return UNSATISFIABLE;

    while(!time_out()) {
//	verify_integrity();
	if (decide_next_branch()) {
	    while (deduce()==CONFLICT) { 
		int blevel = analyze_conflicts();
		if (blevel == 0)
		    return UNSATISFIABLE;
		else
		    backtrack(blevel);
	    }
	}
	else 
	    return SATISFIABLE;
    }
    return TIME_OUT;
}

void CSolver::read_cnf (char * filename)
{
    ifstream in_file(filename);
    if (!in_file) {
	cerr << "Can't open input CNF file " << filename << endl;
	exit(1);
    }
    unsigned num_cls = 0, num_vars = 0;
    
    vector<char> buffer;
    vector<CLiteral> literals;
    bool header_encountered = false;
    char token[64];	
    while (!in_file.eof()) {
	get_line(in_file, buffer);
	char * ptr = &(*buffer.begin());
	if (get_token(ptr, token)) {
	    if (strcmp(token, "c")==0)
		continue;
	    else if (strcmp(token, "p")==0) {
		assert (literals.empty());
		assert (header_encountered == false);
		get_token(ptr, token);
		if (strcmp(token, "cnf") != 0) {
		    cerr << "Format Error, p cnf NumVar NumCls " << endl;
		    exit(1);
		}
		get_token(ptr, token);
		num_vars = atoi(token);
		set_var_number(num_vars);

		get_token(ptr, token);
		num_cls = atoi(token);

		header_encountered = true;
		continue;
	    }
	    else {
		int lit = atoi(token);
		assert (lit <= (int) num_vars || lit >= - (int) num_vars);
		if (lit != 0) {
		    if (lit > 0) 
			literals.push_back(lit + lit);
		    else 
			literals.push_back(1- lit - lit);
		}
		else {
		    add_clause(literals);
		    literals.clear();
		}
	    }
	}
	while (get_token(ptr, token)) {
	    int lit = atoi(token);
	    assert (lit <= (int) num_vars || lit >= - (int) num_vars);
	    if (lit != 0) {
		if (lit > 0) 
		    literals.push_back(lit + lit);
		else 
		    literals.push_back(1- lit - lit);
	    }
	    else {
		add_clause( literals );
		literals.clear();
	    }
	}
    }
    if (!literals.empty()) {
	cerr << "Trailing literals in input without termination " << endl;
	exit(1);
    }
    if ( clauses.size() != num_cls ) 
	cerr << "WARNING : Clause count inconsistant with the header " << endl;
    cout << "Successfully read " << clauses.size() << " Clauses " << endl;
}

void CSolver::print_solution(ostream & o)
{
    o << "A Satisfiable Assignment is: " << endl;
    for (unsigned i=1; i< variables.size(); ++i) {
	CVariable & var = variables[i];
	if (var.value == 0) 
	    o << "-" << i;
	else if (var.value == 1)
	    o << "+" << i;
	else 
	    o << "(" << i << ")";
	o << "  ";
	if (i%10 == 0) 
	    o << endl;
    }
    o << endl;
}


int main(int argc, char * * argv)
{
    if (argc < 2) {
	cerr << "MiniSAT: A Simple SAT Solver " << endl;
	cerr << "Copyright 2003, Microsoft Corp. " << endl << endl;;
	cerr << "Usage: "<< argv[0] << " cnf_file [time_limit]" << endl;
	return 2;
    }

    double init_time = get_cpu_time();
    CSolver solver;
    if (argc == 3) 
	solver.time_limit = atoi(argv[2]);
    else 
	solver.time_limit = 120;	//default to 2 minutes

    solver.read_cnf(argv[1]);
    cout <<"Solving " << argv[1] << " ......" << endl;

    int status = solver.solve();
    switch(status) {
    case SATISFIABLE: 
	cout << "Instance SATISFIABLE" << endl;
	solver.print_solution();
	break;
    case UNSATISFIABLE:
	cout << "Instance UNSATISFIABLE" << endl;
	break;
    case TIME_OUT:
	cout << "Time Out" << endl;
	break;
    }
    cout << "Num Decisions   \t" << solver.num_decisions << endl;
    cout << "Num Conflicts   \t" << solver.num_conflicts << endl;
    cout << "Num Implications\t" << solver.num_implications << endl;
    cout << "Total Runtime   \t" << get_cpu_time() - init_time << endl;
}

