/***********************************************************************/
/*                                                                     */
/*                         Applied Type System                         */
/*                                                                     */
/*                              Hongwei Xi                             */
/*                                                                     */
/***********************************************************************/

/*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 */

/* ****** ****** */

/* Author: Rick Lavoie (coldfury AT cs DOT bu DOT edu) */

/* ****** ****** */

/* Deciding linear inequalities using the Omega test */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <gmp.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

#define OMEGA_TAUTOLOGY 0 /* There is a solution */
#define OMEGA_CONTRADICTION -1 /* There is no solution */
#define OMEGA_UNKNOWN -2 /* Omega test can't decide */
#define OMEGA_REDUNDANT -3 /* This constraint is redundant */

/* Represents an individual constraint */
typedef struct constraint_struct {
  mpz_t* restrict coeff; /* Coefficients */
  mpz_t real_bound;
  long key; /* Hash key */
  struct constraint_struct* restrict next; /* Next in hash link */
} constraint;

/* Represents a set of inequalities */
typedef struct inequalities_struct {
  unsigned int num_variables; /* Number of total variables */
  unsigned int num_constraints; /* Number of actual constraints */
  unsigned int allocated_variables; /* Amount of variables we can fit without expanding */
  unsigned int allocated_constraints; /* Amount of constraints we can fit without expanding */
  unsigned int variable_begin; /* The first "valid" variable */
  unsigned int variable_end; /* The last "valid" variable */
  unsigned int* restrict unit_pos_count; /* Column information to decide which to eliminate */
  unsigned int* restrict unit_neg_count;
  unsigned int* restrict pos_count;
  unsigned int* restrict neg_count;
  char* restrict valid; /* Bitmap of valid variables */
  unsigned int positive_bound_count;
  mpz_t temp;
  mpz_t gcd_temp;
  constraint** restrict hash_table; /* The hash table */
  constraint** restrict constraints; /* The constraints */
} inequalities;

/* For efficiency, only allocate the system once, and then re-use it, expanding as necessary */
static unsigned int omega_is_initialized = 0;
static inequalities main_inequalities;

/* Manipulate the valid bitmap */
#define IS_VALID(x, i) ((x)[(i)/8] & (1 << ((i) % 8)))
#define IS_NOT_VALID(x, i) (!((x)[(i)/8] & (1 << ((i) % 8))))
#define SET_VALID(x, i) ((x)[(i)/8] = ((x)[(i)/8] | (1 << ((i) % 8))))
#define SET_NOT_VALID(x, i) ((x)[(i)/8] = ((x)[(i)/8] & (~(1 << ((i) % 8)))))

#define ALLOC_INCREMENT 32 /* We'll add new constraints in blocks to increase efficiency */
#define ADD_TO_KEY(x, i) (((x) % 16) << (i % (sizeof(long)*2))) /* Use to generate hash keys */

#if 0
/* Debugging functions... */
static void print_constraint(inequalities* const restrict system, constraint* const restrict x)
{
  unsigned int i;

  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i))
      gmp_printf("X%d*%Zd + ", i, x->coeff[i]);
  }
  mpz_neg(system->temp, x->coeff[i]);
  gmp_printf(">= %Zd\n", system->temp);

  return;
}

static void print_constraints(inequalities* const restrict system)
{
  unsigned int i;

  gmp_printf("unit_pos_count = [");
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i))
      gmp_printf("%d,", system->unit_pos_count[i]);
  }
  gmp_printf("]\n");
  
  gmp_printf("unit_neg_count = [");
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i))
      gmp_printf("%d,", system->unit_neg_count[i]);
  }
  gmp_printf("]\n");

  gmp_printf("pos_count = [");
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i))
      gmp_printf("%d,", system->pos_count[i]);
  }
  gmp_printf("]\n");

  gmp_printf("neg_count = [");
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i))
      gmp_printf("%d,", system->neg_count[i]);
  }
  gmp_printf("]\n");

  for (i = 0; i < system->num_constraints; i++)
    print_constraint(system, system->constraints[i]);

  return;
}
#endif

/* 
   Choose a variable from the system to eliminate next. Besides returning the variable index, it also sets
   the two input variables size and exact_chosen. size is set to the maximum number of constraints this
   variable can generate, and exact_chosen is set to 0 or 1 depending of this elimination is exact.
   A size of 0 implies this variable is unbounded.
*/
static unsigned int choose_variable(inequalities* restrict const system, unsigned int* restrict const size,
                                    unsigned int* restrict const exact_chosen)
{
  unsigned int i, last_valid;
  unsigned int pos_total, neg_total, temp_score;
  unsigned int is_exact, best_score, best_index;
  
  best_score = 0;
  best_index = system->variable_begin;
  last_valid = system->variable_end;
  is_exact = 0;

  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i)) {
      last_valid = i;
      pos_total = system->unit_pos_count[i] + system->pos_count[i];
      neg_total = system->unit_neg_count[i] + system->neg_count[i];
      temp_score = pos_total * neg_total;
      if (temp_score == 0) { /* This variable is unbounded */
	*size = 0;
	*exact_chosen = 0;
	return i;
      }
      if ((system->pos_count[i] == 0 || system->neg_count[i] == 0) && (!is_exact || temp_score < best_score)) {
	is_exact = 1;
	best_index = i;
	best_score = temp_score;
      } else if (!is_exact && temp_score < best_score) {
	best_index = i;
	best_score = temp_score;
      }
    } else if (i == system->variable_begin) /* Update the "beginning" */
      system->variable_begin++;
  }

  system->variable_end = last_valid+1; /* Update the "end" */

  *exact_chosen = is_exact;
  *size = best_score;
  return best_index;
}

/* Remove a constraint from the system */
static void remove_constraint(inequalities* restrict const system, const unsigned int target)
{
  constraint* temp;
  constraint* const x = system->constraints[target];
  unsigned int hash_pos, i;
  int temp_sgn;

  /* Fix-up the column information */
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i)) {
      temp_sgn = mpz_sgn(x->coeff[i]);
      if (temp_sgn == 0)
	continue;
      else if (mpz_cmp_ui(x->coeff[i], 1) == 0)
	system->unit_pos_count[i]--;
      else if (mpz_cmp_si(x->coeff[i], -1) == 0)
	system->unit_neg_count[i]--;
      else if (temp_sgn > 0)
	system->pos_count[i]--;
      else
	system->neg_count[i]--;
    }
  }

  if (mpz_sgn(x->real_bound) >= 0)
    system->positive_bound_count--;

  /* Remove it from the hash table */
  if (x->key < 0)
    hash_pos = (-x->key % system->allocated_constraints);
  else 
    hash_pos = (x->key % system->allocated_constraints) + system->allocated_constraints;
  
  temp = system->hash_table[hash_pos];
  if (temp == x)
    system->hash_table[hash_pos] = (constraint*)x->next;
  else {
    while (temp != NULL && temp->next != (struct constraint_struct*)x)
      temp = (constraint*)temp->next;
    if (temp != NULL)
      temp->next = x->next;
  }

  /* "Flip" this constraint to the end and decrement the counter */
  if (target != system->num_constraints-1) {
    temp = system->constraints[target];
    system->constraints[target] = system->constraints[system->num_constraints-1];
    system->constraints[system->num_constraints-1] = temp;
  }

  system->num_constraints--;

  return;
}

/* Insert a constraint into the system, using the hash table to filter if necessary. */
static int insert_and_filter(inequalities* const restrict system, constraint* const restrict x)
{
  constraint* iter;
  constraint* iter2;
  unsigned int i;
  unsigned int hash_pos, hash_pos2;
 
  if (x->key < 0) {
    hash_pos = (-x->key % system->allocated_constraints);
    hash_pos2 = (-x->key % system->allocated_constraints) + system->allocated_constraints;
  } else {
    hash_pos = (x->key % system->allocated_constraints) + system->allocated_constraints;
    hash_pos2 = (x->key % system->allocated_constraints);
  }

  /* Check for duplicate constraints */
  iter = system->hash_table[hash_pos];
  while (iter != NULL && x->key <= iter->key) {
    if (x->key == iter->key) {
      for (i = system->variable_begin; i < system->variable_end; i++) {
	if (IS_VALID(system->valid, i) && (mpz_cmp(x->coeff[i], iter->coeff[i]) != 0))
	  break;
      }
      if (i == system->variable_end) {
	if (mpz_cmp(x->real_bound, iter->real_bound) <= 0) {
	  if (mpz_sgn(iter->real_bound) < 0 && mpz_sgn(x->real_bound) >= 0)
	    system->positive_bound_count++;
	  else if (mpz_sgn(iter->real_bound) >= 0 && mpz_sgn(x->real_bound) < 0)
	    system->positive_bound_count--;
	  mpz_set(iter->real_bound, x->real_bound); /* Tighten this constraint */
	}
	return OMEGA_REDUNDANT;
      }
    }
    iter = (constraint*)iter->next;
  }

  /* Check for contradictory constraints */
  iter2 = system->hash_table[hash_pos2];
  while (iter2 != NULL && -x->key <= iter2->key) {
    if (-x->key == iter2->key) {
      for (i = system->variable_begin; i < system->variable_end; i++) {
	if (IS_VALID(system->valid, i)) {
	  mpz_neg(system->temp, x->coeff[i]);
	  if (mpz_cmp(system->temp, iter2->coeff[i]) != 0)
	    break;
	}
      }
      if (i == system->variable_end) {
	mpz_neg(system->temp, x->real_bound);
	if (mpz_cmp(iter2->real_bound, system->temp) < 0) /* A contradiction */
	  return OMEGA_CONTRADICTION;
      }
    }
    iter2 = (constraint*)iter2->next;
  }
  
  /* Insert it into the table */
  if (iter == NULL) {
    system->hash_table[hash_pos] = x;
    x->next = NULL;
  } else {
    x->next = iter->next;
    iter->next = (struct constraint_struct*)x;
  }

  return OMEGA_TAUTOLOGY;
}

/* Generate a new constraint using the specified variable. */
static int rewrite_inequality(inequalities* const restrict system, constraint* const restrict output, 
			      constraint* const restrict x1, constraint* const restrict x2, const unsigned int var_index)
{
  unsigned int i;
  int temp_sgn, ret;

  mpz_set_ui(system->gcd_temp, 0);
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i)) {
      mpz_mul(output->coeff[i], x1->coeff[var_index], x2->coeff[i]);
      mpz_mul(system->temp, x2->coeff[var_index], x1->coeff[i]);
      mpz_sub(output->coeff[i], output->coeff[i], system->temp);
      mpz_gcd(system->gcd_temp, system->gcd_temp, output->coeff[i]);
    }
  }
  mpz_mul(output->real_bound, x1->coeff[var_index], x2->real_bound);
  mpz_mul(system->temp, x2->coeff[var_index], x1->real_bound);
  mpz_sub(output->real_bound, output->real_bound, system->temp);
  mpz_set_ui(output->coeff[var_index], 0);

  if (mpz_sgn(system->gcd_temp) == 0) { /* The constraint is empty, so its either redundant or contradictory. */
    if (mpz_sgn(output->real_bound) >= 0)
      return OMEGA_REDUNDANT;
    else
      return OMEGA_CONTRADICTION;
  }

  /* Normalize the new constraint and generate the hash key */
  output->key = 0;
  output->next = NULL;
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i)) {
      mpz_divexact(output->coeff[i], output->coeff[i], system->gcd_temp);
      if (mpz_sgn(output->coeff[i]) < 0)
	output->key -= ADD_TO_KEY(-mpz_get_si(output->coeff[i]), i);
      else
	output->key += ADD_TO_KEY(mpz_get_si(output->coeff[i]), i);
    }
  }
  mpz_fdiv_q(output->real_bound, output->real_bound, system->gcd_temp);

  /* Insert it into the hash table */
  ret = insert_and_filter(system, output);
  if (ret != OMEGA_TAUTOLOGY) /* We're done if it wasn't inserted */
    return ret;

  /* Fix up the column information */
  for (i = system->variable_begin; i < system->variable_end; i++) {
    if (IS_VALID(system->valid, i)) {
      temp_sgn = mpz_sgn(output->coeff[i]);
      if (temp_sgn == 0)
	continue;
      else if (mpz_cmp_ui(output->coeff[i], 1) == 0)
	system->unit_pos_count[i]++;
      else if (mpz_cmp_si(output->coeff[i], -1) == 0)
	system->unit_neg_count[i]++;
      else if (temp_sgn > 0)
	system->pos_count[i]++;
      else
	system->neg_count[i]++;
    }
  }

  if (mpz_sgn(output->real_bound) >= 0)
    system->positive_bound_count++;

  return OMEGA_TAUTOLOGY;
}

/* Allocate more space for constraints in the system */
static void enlarge_constraint_space(inequalities* const restrict system, const unsigned int increment)
{
  unsigned int i, j;
  const unsigned int old_size = system->allocated_constraints;
  const unsigned int new_size = system->allocated_constraints+increment;
  constraint** old_hash;
  constraint* temp;
  constraint* temp2;

  system->constraints = realloc(system->constraints, sizeof(constraint*)*new_size);
  if (system->constraints == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to allocate constraints!\n");
    exit(1);
  }

  for (i = old_size; i < new_size; i++) {
    system->constraints[i] = malloc(sizeof(constraint));
    if (system->constraints[i] == NULL) {
      fprintf(stderr, "OMEGA FATAL ERROR! Unable to allocate constraint row!\n");
      exit(1);
    }
    system->constraints[i]->coeff = malloc(sizeof(mpz_t)*system->allocated_variables);
    if (system->constraints[i]->coeff == NULL) {
      fprintf(stderr, "OMEGA FATAL ERROR! Unable to allocate coefficient row!\n");
      exit(1);
    }
    for (j = 0; j < system->allocated_variables; j++)
      mpz_init(system->constraints[i]->coeff[j]);
    mpz_init(system->constraints[i]->real_bound);
  }

  old_hash = system->hash_table;
  system->hash_table = malloc(sizeof(constraint*)*new_size*2);
  if (system->hash_table == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to allocate hash table!\n");
    exit(1);
  }

  memset(system->hash_table, 0, sizeof(constraint*)*new_size*2);

  system->allocated_constraints = new_size;

  /* Re-hash the constraints into the new table */
  for (i = 0; i < old_size*2; i++) {
    temp = old_hash[i];
    while (temp != NULL) {
      temp2 = (constraint*)temp->next;
      temp->next = NULL;
      insert_and_filter(system, temp);
      temp = temp2;
    }
  }

  free(old_hash);

  return;
}

/* Add more space for variables in the system */
static void enlarge_variable_space(inequalities* const restrict system, const unsigned int increment)
{
  const unsigned int new_size = system->allocated_variables+increment;
  unsigned int i, j;

  system->valid = realloc(system->valid, (new_size/8)+1);
  if (system->valid == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to allocate valid bitmap!\n");
    exit(1);
  }

  for (i = 0; i < system->allocated_constraints; i++) {
    system->constraints[i]->coeff = realloc(system->constraints[i]->coeff, sizeof(mpz_t)*new_size);
    if (system->constraints[i]->coeff == NULL) {
      fprintf(stderr, "OMEGA FATAL ERROR! Unable to allocate new coefficient vector!\n");
      exit(1);
    }
    for (j = system->allocated_constraints; j < new_size; j++)
      mpz_init(system->constraints[i]->coeff[j]);
  }

  system->unit_pos_count = realloc(system->unit_pos_count, sizeof(unsigned int)*new_size);
  if (system->unit_pos_count == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to alloc unit_pos_count vector!\n");
    exit(1);
  }

  system->unit_neg_count = realloc(system->unit_neg_count, sizeof(unsigned int)*new_size);
  if (system->unit_neg_count == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to alloc unit_neg_count vector!\n");
    exit(1);
  }

  system->pos_count = realloc(system->pos_count, sizeof(unsigned int)*new_size);
  if (system->pos_count == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to alloc pos_count vector!\n");
    exit(1);
  }

  system->neg_count = realloc(system->neg_count, sizeof(unsigned int)*new_size);
  if (system->neg_count == NULL) {
    fprintf(stderr, "OMEGA FATAL ERROR! Unable to alloc neg_count vector!\n");
    exit(1);
  }

  system->allocated_variables = new_size;

  return;
}

/* Allocate a new system */
static void allocate_inequalities(inequalities* const restrict system, const unsigned int variable, const unsigned int constraints)
{
  system->num_variables = 0;
  system->num_constraints = 0;
  system->allocated_variables = 0;
  system->allocated_constraints = 0;
  system->variable_begin = 0;
  system->variable_end = 0;
  system->positive_bound_count = 0;
  system->valid = NULL;
  system->hash_table = NULL;
  system->constraints = NULL;
  system->unit_pos_count = NULL;
  system->unit_neg_count = NULL;
  system->pos_count = NULL;
  system->neg_count = NULL;
  
  mpz_init(system->temp);
  mpz_init(system->gcd_temp);

  enlarge_variable_space(system, variable+ALLOC_INCREMENT);
  enlarge_constraint_space(system, constraints+ALLOC_INCREMENT);

  return;
}

/* Using the variable we've chosen, generate all the new constraints from it. */
static int cross_variables(inequalities* const restrict system, const unsigned int variable, unsigned int new_count)
{
  int ret;
  unsigned int i, j;
  unsigned int added_constraints;

  if (system->num_constraints+new_count >= system->allocated_constraints)
    enlarge_constraint_space(system, new_count+ALLOC_INCREMENT);

  added_constraints = 0;
  SET_NOT_VALID(system->valid, variable);
  if (variable == system->variable_begin)
    system->variable_begin++;

  for (i = 0; (i < system->num_constraints) && (added_constraints < new_count); i++) {
    if (mpz_sgn(system->constraints[i]->coeff[variable]) > 0) {
      for (j = 0; (j < system->num_constraints) && (added_constraints < new_count); j++) {
	if (i != j && (mpz_sgn(system->constraints[j]->coeff[variable]) < 0)) {
	  ret = rewrite_inequality(system, system->constraints[system->num_constraints+added_constraints],
				   system->constraints[i], system->constraints[j], variable);
	  if (ret == OMEGA_CONTRADICTION) /* No more work needs to be done */
	    return OMEGA_CONTRADICTION;
	  else if (ret == OMEGA_REDUNDANT) /* This constraint is redundant, so don't count it */
	    new_count--;
	  else
	    added_constraints++;
	}
      }
    }
  }

  system->num_constraints += added_constraints;

  return OMEGA_TAUTOLOGY;
}

/* Remove all constraints from the system which contain the specified variable. */
static void remove_variable(inequalities* const restrict system, const unsigned int variable)
{
  unsigned int i;
  unsigned int count = system->unit_pos_count[variable] + system->unit_neg_count[variable] + 
    system->pos_count[variable] + system->neg_count[variable];

  /* We know the count of constraints (taken from the column info), so we can bail out early */
  for (i = 0; (i < system->num_constraints && count > 0); i++) {
    if (mpz_sgn(system->constraints[i]->coeff[variable]) != 0) {
      mpz_set_ui(system->constraints[i]->coeff[variable], 0);
      remove_constraint(system, i);
      i--; 
      count--;
    }
  }

  return;
}

/* The main loop of the omega test. Keep eliminating variables until we reach a tautology or a contradiction. */
static int do_omega(inequalities* const restrict system)
{
  int ret;
  unsigned int new_constraint_count, chosen_variable;
  unsigned int is_exact_elimination;

  while (1) {
    while (1) { /* Keep looping until we've removed all unbounded variables */
      if (system->num_constraints <= 1 || system->positive_bound_count == system->num_constraints) /* A single constraint is always solvable */
	return OMEGA_TAUTOLOGY;
      chosen_variable = choose_variable(system, &new_constraint_count, &is_exact_elimination);
      if (new_constraint_count == 0) { /* This variable is unbounded */
	SET_NOT_VALID(system->valid, chosen_variable);
        if (chosen_variable == system->variable_begin)
          system->variable_begin++;
	remove_variable(system, chosen_variable); /* Just remove it */
      } else
	break; /* We chose a bounded variable */
    }

    /* I haven't implemented the non-exact case for simplicity reasons. It almost never occurs. */
    if (!is_exact_elimination) 
      return OMEGA_UNKNOWN;
    
    /* Generate all the new constraints using this variable */
    ret = cross_variables(system, chosen_variable, new_constraint_count);
    if (ret < 0)
      return ret;

    /* Now remove all the old constraints using this variable */
    remove_variable(system, chosen_variable);
  }

  return OMEGA_TAUTOLOGY;
}

/* Read a row in from the ocaml code, and initialize it. */
static int init_constraint(inequalities* const restrict system, constraint* const restrict output, value x)
{
  CAMLparam1(x);
  unsigned int i;
  int temp_val, is_zero, ret;
  char temp_val2, temp_val3;

  /* Insert into row and generate hash key */
  output->next = NULL;
  output->key = 0;
  is_zero = 1;
  for (i = 0; i < system->num_variables; i++) {
    mpz_set_str(output->coeff[i], String_val(Field(x, i+1)), 10);
    temp_val = mpz_get_ui(output->coeff[i]);
    if (mpz_sgn(output->coeff[i]) > 0) {
      output->key += ADD_TO_KEY(temp_val, i);
      is_zero = 0;
    } else if (mpz_sgn(output->coeff[i]) < 0) {
      output->key -= ADD_TO_KEY(-temp_val, i);
      is_zero = 0;
    }
  }
  mpz_set_str(output->real_bound, String_val(Field(x, 0)), 10);

  /* The constraint is empty */
  if (is_zero) {
    if (String_val(Field(x, 0))[0] != '-')
      CAMLreturn(OMEGA_REDUNDANT);
    else
      CAMLreturn(OMEGA_CONTRADICTION);
  }

  /* Insert it */
  ret = insert_and_filter(system, output);
  if (ret != OMEGA_TAUTOLOGY)
    CAMLreturn(ret);

  /* If the insertion was successful, then generate the column information */
  for (i = 0; i < system->num_variables; i++) {
    temp_val2 = String_val(Field(x, i+1))[0];
    temp_val3 = String_val(Field(x, i+1))[1];
    if (temp_val2 == '0')
      continue;
    else if (temp_val2 == '1')
      system->unit_pos_count[i]++;
    else if (temp_val2 == '-' && temp_val3 == '1')
      system->unit_neg_count[i]++;
    else if (temp_val2 != '-')
      system->pos_count[i]++;
    else
      system->neg_count[i]++;
  }

  if (String_val(Field(x, 0))[0] != '-')
    system->positive_bound_count++;

  CAMLreturn(OMEGA_TAUTOLOGY);
}

/* Entry-point from the Ocaml code */
value caml_solve_veclist_omega(value constraints)
{
  CAMLparam1(constraints);
  CAMLlocal1(list_ptr);
  unsigned int i, n;
  int ret;

  list_ptr = constraints;
  n = Wosize_val(Field(list_ptr, 0))-1;

  /* If this is the first time, allocate memory */
  if (!omega_is_initialized) {
    allocate_inequalities(&main_inequalities, n+ALLOC_INCREMENT, ALLOC_INCREMENT);
    omega_is_initialized = 1;
  }

  main_inequalities.num_constraints = 0;
  main_inequalities.num_variables = n;
  main_inequalities.variable_begin = 0;
  main_inequalities.variable_end = n;
  main_inequalities.positive_bound_count = 0;

  /* Make sure we have enough space for the variables */
  if (main_inequalities.allocated_variables < n)
    enlarge_variable_space(&main_inequalities, n+ALLOC_INCREMENT);

  for (i = 0; i < n; i++)
    SET_VALID(main_inequalities.valid, i);

  /* Blank all the running information */
  memset(main_inequalities.hash_table, 0, sizeof(constraint*)*main_inequalities.allocated_constraints*2);
  memset(main_inequalities.unit_pos_count, 0, sizeof(unsigned int)*main_inequalities.allocated_variables);
  memset(main_inequalities.unit_neg_count, 0, sizeof(unsigned int)*main_inequalities.allocated_variables);
  memset(main_inequalities.pos_count, 0, sizeof(unsigned int)*main_inequalities.allocated_variables);
  memset(main_inequalities.neg_count, 0, sizeof(unsigned int)*main_inequalities.allocated_variables);

  /* Until we reach the end of the list, insert them */
  while (list_ptr != Val_int(0)) {
    if (main_inequalities.num_constraints >= main_inequalities.allocated_constraints)
      enlarge_constraint_space(&main_inequalities, ALLOC_INCREMENT);
    ret = init_constraint(&main_inequalities, main_inequalities.constraints[main_inequalities.num_constraints], Field(list_ptr, 0));
    if (ret == OMEGA_CONTRADICTION)
      CAMLreturn(Val_int(OMEGA_CONTRADICTION));
    else if (ret != OMEGA_REDUNDANT)
      main_inequalities.num_constraints++;
    list_ptr = Field(list_ptr, 1);
  }

  /* Run omega and report the result */
  ret = do_omega(&main_inequalities);
    
  CAMLreturn(Val_int(ret));
}

/* End of atsOmega.c */

