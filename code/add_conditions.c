#include <stddef.h>
#include "cnf.h"

//
// LOGIN: xstigl00
//

// Tato funkce je prikladem pouziti funkci create_new_clause, add_literal_to_clause a add_clause_to_formula
// Vysvetleni, co dela, naleznete v zadani
void example_condition(CNF *formula, unsigned num_of_subjects, unsigned num_of_semesters) {
    assert(formula != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    for (unsigned subject_i = 0; subject_i < num_of_subjects; ++subject_i) {
        for (unsigned semester_j = 0; semester_j < num_of_semesters; ++semester_j) {
            // vytvori novou klauzuli
            Clause *example_clause = create_new_clause(num_of_subjects, num_of_semesters);
            // vlozi do klauzule literal x_{i,j}
            add_literal_to_clause(example_clause, true, subject_i, semester_j);
            // vlozi do klauzule literal ~x_{i,j}
            add_literal_to_clause(example_clause, false, subject_i, semester_j);
            // prida klauzuli do formule
            add_clause_to_formula(example_clause, formula);
        }
    }
}

// Tato funkce by mela do formule pridat klauzule predstavujici podminku a)
// Predmety jsou reprezentovany cisly 0, 1, ..., num_of_subjects-1
// Semestry jsou reprezentovany cisly 0, 1, ..., num_of_semesters-1
void each_subject_enrolled_at_least_once(
    CNF *formula,
    unsigned num_of_subjects,
    unsigned num_of_semesters
) {
    assert(formula != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    // (x_0,0 v x_1,0 v x_2,0 v ...) ^ (x_1,0 v x_1,1 v x_1,2 v ...) ^ ...
    for (size_t sub = 0; sub < num_of_subjects; ++sub) {
        Clause *c = create_new_clause(num_of_subjects, num_of_semesters);
        for (size_t sem = 0; sem < num_of_semesters; ++sem) {
            add_literal_to_clause(c, true, sub, sem);
        }
        add_clause_to_formula(c, formula);
    }
}

// Tato funkce by mela do formule pridat klauzule predstavujici podminku b)
// Predmety jsou reprezentovany cisly 0, 1, ..., num_of_subjects-1
// Semestry jsou reprezentovany cisly 0, 1, ..., num_of_semesters-1
void each_subject_enrolled_at_most_once(
    CNF *formula,
    unsigned num_of_subjects,
    unsigned num_of_semesters
) {
    assert(formula != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    // (x_0,0 ^ !x_0,1 ^ !x_0,2) v (!x_0,0 ^ x_0,1 ^ !x_0,2) v
    // (!x_0,0 ^ !x_0,1 ^ x_0,2) v
    // (x_1,0 ^ !x_1,1 ^ !x_1,2) v (!x_1,0 ^ x_1,1 ^ !x_1,2) v
    // (!x_1,0 ^ !x_1,1 ^ x_1,2) v
    // ...
    // <~> (it is already assumed that each subject is enrolled at leas once)
    // (!x_0,0 v !x_0,1) ^ (!x_0,0 v !x_0,2) ^ (!x_0,1 v !x_0,2) ^
    // (!x_1,0 v !x_1,1) ^ (!x_1,0 v !x_1,2) ^ (!x_1,1 v !x_1,2) ^
    // ...
    for (size_t sub = 0; sub < num_of_subjects; ++sub) {
        for (size_t i = 0; i < num_of_semesters; ++i) {
            for (size_t j = i + 1; j < num_of_semesters; ++j) {
                Clause *c = create_new_clause(
                    num_of_subjects,
                    num_of_semesters
                );
                add_literal_to_clause(c, false, sub, i);
                add_literal_to_clause(c, false, sub, j);
                add_clause_to_formula(c, formula);
            }
        }
    }
}


// Tato funkce by mela do formule pridat klauzule predstavujici podminku c)
// Promenna prerequisities obsahuje pole s poctem prvku rovnym
// num_of_prerequisities
// Predmety jsou reprezentovany cisly 0, 1, ..., num_of_subjects-1
// Semestry jsou reprezentovany cisly 0, 1, ..., num_of_semesters-1
void add_prerequisities_to_formula(
    CNF *formula,
    Prerequisity* prerequisities,
    unsigned num_of_prerequisities,
    unsigned num_of_subjects,
    unsigned num_of_semesters
) {
    assert(formula != NULL);
    assert(prerequisities != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    for (unsigned i = 0; i < num_of_prerequisities; ++i) {
        // prerequisities[i].earlier_subject je predmet, ktery by si mel
        // student zapsat v nekterem semestru pred predmetem
        // prerequisities[i].later_subject

        unsigned e = prerequisities[i].earlier_subject;
        unsigned l = prerequisities[i].later_subject;

        // e = earlier, l = later
        // (x_l,3 ^ !x_e,3) v (x_l,2 ^ !x_e,3 ^ !x_e,2) v
        // (x_l,1 ^ !x_e,3 ^ !x_e,2 ^ !x_e,1)
        // <=>
        // !x_e,3 ^ (!x_e,2 v x_l,3) ^ (!x_e,1 v x_l,3 v x_l,2) ^
        // (x_e,3 v x_e,2 v x_e,1)

        // !x_e3
        Clause *c = create_new_clause(num_of_subjects, num_of_semesters);
        add_literal_to_clause(c, false, e, num_of_semesters - 1);
        add_clause_to_formula(c, formula);

        // (x_e3 v x_e,2 v x_e,1)
        Clause *a_l = create_new_clause(num_of_subjects, num_of_semesters);
        add_literal_to_clause(a_l, true, l, num_of_semesters - 1);

        // avoid overflow
        if (num_of_semesters == 1) {
            add_clause_to_formula(a_l, formula);
            return;
        }

        for (size_t k = num_of_semesters - 2; k > 0; --k) {
            // (!x_e,2 v x_l,3) ^ (!x_e,1 v x_l,3 v x_l,2)
            Clause *c = create_new_clause(num_of_subjects, num_of_semesters);
            add_literal_to_clause(c, false, e, k);
            for (size_t j = k + 1; j < num_of_semesters; ++j) {
                add_literal_to_clause(c, true, l, j);
            }
            add_clause_to_formula(c, formula);

            add_literal_to_clause(a_l, true, l, k);
        }
        add_clause_to_formula(a_l, formula);
    }
}
