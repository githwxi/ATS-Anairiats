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

/* Solving Integer Linear Programming problems using Simplex and the Branch-and-Bound method */

#include <stdlib.h>
#include <stdio.h>
#include <gmp.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>

#define ALLOC_INCREMENT 32 /* How much space we'll keep in reserve */

#define SIMPLEX_INFEASIBLE -1
#define SIMPLEX_UNBOUNDED -2

/* Bitfield manipulations */
#define IN_N(x, i) ((x)[(i)/8] & (1 << ((i) % 8)))
#define IN_B(x, i) (!((x)[(i)/8] & (1 << ((i) % 8))))
#define ADD_TO_N(x, i) ((x)[(i)/8] = ((x)[(i)/8] | (1 << ((i) % 8))))
#define ADD_TO_B(x, i) ((x)[(i)/8] = ((x)[(i)/8] & (~(1 << ((i) % 8)))))

#define IS_INFINITY(x, i) ((x)[(i)/8] & (1 << ((i) % 8)))
#define IS_NOT_INFINITY(x, i) (!((x)[(i)/8] & (1 << ((i) % 8))))
#define SET_INFINITY(x, i) ((x)[(i)/8] = ((x)[(i)/8] | (1 << ((i) % 8))))
#define SET_NOT_INFINITY(x, i) ((x)[(i)/8] = ((x)[(i)/8] & (~(1 << ((i) % 8)))))

/* Represents the constraints in slack-form */
typedef struct slack_form_struct {
  unsigned int size;
  unsigned int allocated_size;
  unsigned int num_variables;
  unsigned char* restrict basic_set;
  unsigned char* restrict is_infinity;
  mpq_t** restrict A;
  mpq_t* restrict B;
  mpq_t* restrict C;
  mpq_t* restrict backupC; /* We store a backup of the constraints to ensure we can easily compute the basic solution */
  mpq_t V;
  mpq_t backupV;
  mpq_t* restrict lambda;
  mpq_t* restrict X;
  mpq_t temp;
} slack_form;

static int simplex_is_initialized = 0;
static slack_form main_slack;

static void mpq_floor(mpq_t dest, mpq_t x, mpq_t temp)
{
  mpz_mod(mpq_numref(temp), mpq_numref(x), mpq_denref(x));
  mpz_sub(mpq_numref(dest), mpq_numref(x), mpq_numref(temp));
  mpz_set(mpq_denref(dest), mpq_denref(x));
  mpq_canonicalize(dest);
  return;
}

static void mpq_ceiling(mpq_t dest, mpq_t x, mpq_t temp)
{
  mpz_mod(mpq_numref(temp), mpq_numref(x), mpq_denref(x));
  mpz_sub(mpq_numref(temp), mpq_denref(x), mpq_numref(temp));
  mpz_add(mpq_numref(dest), mpq_numref(x), mpq_numref(temp));
  mpz_set(mpq_denref(dest), mpq_denref(x));
  mpq_canonicalize(dest);
  return;
}

/* Add more space to the matrix, to ensure we can add a constraint or variable */
static void enlarge_slack_form(slack_form* const restrict slack, const unsigned int increment)
{
  unsigned int i, j;
  const unsigned int new_size = slack->allocated_size+increment;

  slack->basic_set = realloc(slack->basic_set, (new_size/8)+1);
  if (slack->basic_set == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc basic set!\n");
    exit(1);
  }

  slack->A = realloc(slack->A, sizeof(mpq_t*)*new_size);
  if (slack->A == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc A array!\n");
    exit(1);
  }

  for (i = 0; i < slack->allocated_size; i++) {
    slack->A[i] = realloc(slack->A[i], sizeof(mpq_t)*new_size);
    if (slack->A[i] == NULL) {
      fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc A row!\n");
      exit(1);
    }
    for (j = slack->allocated_size; j < new_size; j++)
      mpq_init(slack->A[i][j]);
  }

  for (i = slack->allocated_size; i < new_size; i++) {
    slack->A[i] = malloc(sizeof(mpq_t)*new_size);
    if (slack->A[i] == NULL) {
      fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc A row!\n");
      exit(1);
    }
    for (j = 0; j < new_size; j++)
      mpq_init(slack->A[i][j]);
  }

  slack->B = realloc(slack->B, sizeof(mpq_t)*new_size);
  if (slack->B == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc B array!\n");
    exit(1);
  }

  for (i = slack->allocated_size; i < new_size; i++)
    mpq_init(slack->B[i]);

  slack->C = realloc(slack->C, sizeof(mpq_t)*new_size);
  if (slack->C == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc C array!\n");
    exit(1);
  }

  for (i = slack->allocated_size; i < new_size; i++)
    mpq_init(slack->C[i]);

  slack->backupC = realloc(slack->backupC, sizeof(mpq_t)*new_size);
  if (slack->backupC == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc backupC array!\n");
    exit(1);
  }

  for (i = slack->allocated_size; i < new_size; i++)
    mpq_init(slack->backupC[i]);

  slack->lambda = realloc(slack->lambda, sizeof(mpq_t)*new_size);
  if (slack->lambda == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc lambda array!\n");
    exit(1);
  }

  for (i = slack->allocated_size; i < new_size; i++)
    mpq_init(slack->lambda[i]);

  slack->X = realloc(slack->X, sizeof(mpq_t)*new_size);
  if (slack->X == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc X array!\n");
    exit(1);
  }

  for (i = slack->allocated_size; i < new_size; i++)
    mpq_init(slack->X[i]);

  slack->is_infinity = realloc(slack->is_infinity, (new_size/8)+1);
  if (slack->is_infinity == NULL) {
    fprintf(stderr, "SIMPLEX FATAL ERROR! Unable to re-alloc is_infinity array!\n");
    exit(1);
  }

  slack->allocated_size = new_size;

  return;
}

/* Initialize the fields of the given slack form */
static void alloc_slack_form(slack_form* const restrict slack, const unsigned int size)
{
  slack->size = 0;
  slack->allocated_size = 0;
  slack->basic_set = NULL;
  slack->A = NULL;
  slack->B = NULL;
  slack->C = NULL;
  slack->backupC = NULL;
  slack->lambda = NULL;
  slack->X = NULL;
  slack->is_infinity = NULL;

  mpq_init(slack->temp);
  mpq_init(slack->V);
  mpq_init(slack->backupV);

  enlarge_slack_form(slack, size+ALLOC_INCREMENT);

  return;
}

#if 0
static void free_slack_form(slack_form* const restrict slack)
{
  unsigned int i, j;

  if (slack->basic_set)
    free(slack->basic_set);
  if (slack->is_infinity)
    free(slack->is_infinity);

  mpq_clear(slack->temp);
  mpq_clear(slack->V);
  mpq_clear(slack->backupV);

  if (slack->A) {
    for (i = 0; i < slack->allocated_size; i++) {
      if (slack->A[i]) {
	for (j = 0; j < slack->allocated_size; j++)
	  mpq_clear(slack->A[i][j]);
	free(slack->A[i]);
      }
    }
    free(slack->A);
  }

  if (slack->B) {
    for (i = 0; i < slack->allocated_size; i++)
      mpq_clear(slack->B[i]);
    free(slack->B);
  }

  if (slack->C) {
    for (i = 0; i < slack->allocated_size; i++)
      mpq_clear(slack->C[i]);
    free(slack->C);
  }

  if (slack->backupC) {
    for (i = 0; i < slack->allocated_size; i++)
      mpq_clear(slack->backupC[i]);
    free(slack->backupC);
  }

  if (slack->lambda) {
    for (i = 0; i < slack->allocated_size; i++)
      mpq_clear(slack->lambda[i]);
    free(slack->lambda);
  }

  if (slack->X) {
    for (i = 0; i < slack->allocated_size; i++)
      mpq_clear(slack->X[i]);
    free(slack->X);
  }

  slack->size = 0;
  slack->allocated_size = 0;
  slack->num_variables = 0;
  slack->basic_set = NULL;
  slack->A = NULL;
  slack->B = NULL;
  slack->C = NULL;
  slack->backupC = NULL;
  slack->lambda = NULL;
  slack->X = NULL;
  slack->is_infinity = NULL;

  return;
}
#endif

/* The heart of the simplex method. Pivot a variable into a constraint and vice-versa. */
static void do_pivot(slack_form* const restrict slack, const unsigned int leaving, const unsigned int entering)
{
  unsigned int i, j;

  mpq_div(slack->B[entering], slack->B[leaving], slack->A[leaving][entering]);

  for (j = 0; j < slack->size; j++) {
    if (IN_N(slack->basic_set, j) && j != entering)
      mpq_div(slack->A[entering][j], slack->A[leaving][j], slack->A[leaving][entering]);
  }

  mpq_inv(slack->A[entering][leaving], slack->A[leaving][entering]);

  for (i = 0; i < slack->size; i++) {
    if (IN_B(slack->basic_set, i) && i != leaving) {
      mpq_mul(slack->temp, slack->A[i][entering], slack->B[entering]);
      mpq_sub(slack->B[i], slack->B[i], slack->temp);
      for (j = 0; j < slack->size; j++) {
	if (IN_N(slack->basic_set, j) && j != entering) {
	  mpq_mul(slack->temp, slack->A[i][entering], slack->A[entering][j]);
	  mpq_sub(slack->A[i][j], slack->A[i][j], slack->temp);
	}
      }
      mpq_neg(slack->temp, slack->A[i][entering]);
      mpq_mul(slack->A[i][leaving], slack->temp, slack->A[entering][leaving]);
    }
  }
  
  mpq_mul(slack->temp, slack->C[entering], slack->B[entering]);
  mpq_add(slack->V, slack->V, slack->temp);

  for (j = 0; j < slack->size; j++) {
    if (IN_N(slack->basic_set, j) && j != entering) {
      mpq_mul(slack->temp, slack->C[entering], slack->A[entering][j]);
      mpq_sub(slack->C[j], slack->C[j], slack->temp);
    }
  }

  mpq_neg(slack->temp, slack->C[entering]);
  mpq_mul(slack->C[leaving], slack->temp, slack->A[entering][leaving]);

  /* If we're using a backup, perform the pivot on that too */
  if (slack->backupC) {
    mpq_mul(slack->temp, slack->backupC[entering], slack->B[entering]);
    mpq_add(slack->backupV, slack->backupV, slack->temp);
    
    for (j = 0; j < slack->size; j++) {
      if (IN_N(slack->basic_set, j) && j != entering) {
	mpq_mul(slack->temp, slack->backupC[entering], slack->A[entering][j]);
	mpq_sub(slack->backupC[j], slack->backupC[j], slack->temp);
      }
    }
    
    mpq_neg(slack->temp, slack->backupC[entering]);
    mpq_mul(slack->backupC[leaving], slack->temp, slack->A[entering][leaving]);
  }
  
  ADD_TO_N(slack->basic_set, leaving);
  ADD_TO_B(slack->basic_set, entering);

  return;
}

/* Ensure that the given variable is in a row. */
static void bring_into_row(slack_form* const restrict slack, const unsigned int target, const unsigned int begin, const unsigned int end)
{
  unsigned int i;

  if (IN_N(slack->basic_set, target)) {
    for (i = begin; i < end; i++) {
      if (IN_B(slack->basic_set, i) && (mpq_cmp_ui(slack->A[i][target], 0, 1) != 0))  {
	do_pivot(slack, i, target);
	return;
      }
    }
  }

  return;
}

/* Ensure that the given variable is in a column. */
static void bring_into_column(slack_form* const restrict slack, const unsigned int target, const unsigned int begin, const unsigned int end)
{
  unsigned int i;

  if (IN_B(slack->basic_set, target)) {
    for (i = begin; i < end; i++) {
      if (IN_N(slack->basic_set, i) && (mpq_cmp_ui(slack->A[target][i], 0, 1) != 0)) {
	do_pivot(slack, target, i);
	return;
      }
    }
  }

  return;
}

/* Loop around until all constraints are non-positive */
static int do_simplex_loop(slack_form* const restrict slack)
{
  unsigned int e, i, l, min_index, is_set;

  while (1) {
    for (e = 0; e < slack->size; e++) {
      if (IN_N(slack->basic_set, e) && (mpq_sgn(slack->C[e]) > 0))
	break;
    }

    if (e == slack->size)
      break;

    for (i = 0; i < slack->size; i++) {
      if (IN_B(slack->basic_set, i)) {
	if (mpq_sgn(slack->A[i][e]) > 0) {
	  mpq_div(slack->lambda[i], slack->B[i], slack->A[i][e]);
	  SET_NOT_INFINITY(slack->is_infinity, i);
	} else {
	  mpq_set_ui(slack->lambda[i], 0, 1);
	  SET_INFINITY(slack->is_infinity, i);
	}
      }
    }

    is_set = 0;
    min_index = 0;
    for (l = 0; l < slack->size; l++) {
      if (IN_B(slack->basic_set, l)) {
	if (is_set) {
	  if (IS_INFINITY(slack->is_infinity, min_index) && IS_NOT_INFINITY(slack->is_infinity, l))
	    min_index = l;
	  else if (IS_NOT_INFINITY(slack->is_infinity, l) && mpq_cmp(slack->lambda[l], slack->lambda[min_index]) < 0)
	    min_index = l;
	} else {
	  min_index = l;
	  is_set = 1;
	}
      }
    }

    if (IS_INFINITY(slack->is_infinity, min_index))
      return SIMPLEX_UNBOUNDED;

    do_pivot(slack, min_index, e);
  }

  for (i = 0; i < slack->size; i++) {
    if (IN_B(slack->basic_set, i))
      mpq_set(slack->X[i], slack->B[i]);
    else
      mpq_set_ui(slack->X[i], 0, 1);
  }

  return 0;
}

/* Get a basic initial solution */
static int init_simplex(slack_form* const restrict slack)
{
  unsigned int i, min_index, is_set;
  int ret;
  mpq_t* temp;

  /* Find a minimum constraint */
  min_index = 0;
  is_set = 0;
  for (i = 0; i < slack->size; i++) {
    if (IN_B(slack->basic_set, i)) {
      if (is_set) {
	if (mpq_cmp(slack->B[i], slack->B[min_index]) < 0)
	  min_index = i;
      } else {
	is_set = 1;
	min_index = i;
      }
    }
  }

  if (mpq_sgn(slack->B[min_index]) >= 0)
    return 0;

  /* Zero solution does not suffice, we need to add a variable. */
  if (slack->size == slack->allocated_size)
    enlarge_slack_form(slack, ALLOC_INCREMENT);
  ADD_TO_N(slack->basic_set, slack->size);
  for (i = 0; i < slack->size; i++) {
    if (IN_B(slack->basic_set, i))
      mpq_set_si(slack->A[i][slack->size], -1, 1);
  }
  temp = slack->backupC; /* Save the original constraint */
  slack->backupC = slack->C;
  slack->C = temp;
  mpq_set(slack->backupV, slack->V);
  mpq_set_ui(slack->V, 0, 1);
  for (i = 0; i < slack->size; i++) { /* Now clear it out and add the new one */
    if (IN_N(slack->basic_set, i))
      mpq_set_ui(slack->C[i], 0, 1);
  }
  mpq_set_si(slack->C[slack->size], -1, 1);
  slack->size++;

  do_pivot(slack, min_index, slack->size-1);
  ret = do_simplex_loop(slack); /* Get the initial basic solution */

  if (ret < 0)
    goto end;
  if (mpq_cmp_ui(slack->X[slack->size-1], 0, 1) != 0) {
    ret = SIMPLEX_INFEASIBLE;
    goto end;
  }

  ret = 0;

 end:
  /* Remove the added variable and re-establish the original constraint */
  bring_into_column(slack, slack->size-1, 0, slack->size-1);
  slack->size--;
  temp = slack->C;
  slack->C = slack->backupC;
  slack->backupC = temp;
  mpq_set(slack->V, slack->backupV);

  return ret;
}

/* Entry point to the simplex method */
static int do_simplex(slack_form* const restrict slack)
{
  int ret;
  mpq_t* temp;

  ret = init_simplex(slack);
  if (ret < 0)
    return ret;

  /* Set the backup constraint to NULL because we don't need it here */
  temp = slack->backupC;
  slack->backupC = NULL;
  ret = do_simplex_loop(slack); 
  slack->backupC = temp;
  if (ret < 0)
    return ret;

  return 0;
}

/* 
   Use the branch-and-bound method to find an integer solution to the constraints.
   This name is a misnomer, since we do not perform any bounding here. We return
   immediately when we find a solution, not the optimal solution.
*/
static int branch_and_bound(slack_form* const restrict slack)
{
  int i, non_integral, ret;
  mpq_t temp;

  ret = do_simplex(slack);
  if (ret < 0)
    return ret;
  
  /* Look for a non-integral result */
  for (non_integral = 0; non_integral < slack->num_variables; non_integral++) {
    mpq_canonicalize(slack->X[non_integral]);
    if (mpz_cmp_ui(mpq_denref(slack->X[non_integral]), 1) != 0)
      break;
  }

  /* Success! */
  if (non_integral == slack->num_variables)
    return 0;
  
  mpq_init(temp);
  mpq_set(temp, slack->X[non_integral]);

  /* We found one, we need to add a constraint and branch */
  if (slack->allocated_size == slack->size)
    enlarge_slack_form(slack, ALLOC_INCREMENT);
  
  /* First try less than */
  bring_into_column(slack, non_integral, 0, slack->size);
  ADD_TO_B(slack->basic_set, slack->size);
  for (i = 0; i < slack->size; i++)
    mpq_set_ui(slack->A[slack->size][i], 0, 1);
  mpq_set_ui(slack->A[slack->size][non_integral], 1, 1);
  mpq_floor(slack->B[slack->size], temp, slack->temp);
  slack->size++;

  ret = branch_and_bound(slack);
  if (ret != SIMPLEX_INFEASIBLE)
    goto end;

  bring_into_row(slack, slack->size-1, 0, slack->size-1);
  bring_into_column(slack, non_integral, 0, slack->size-1);

  /* Now try greater than */
  for (i = 0; i < slack->size; i++)
    mpq_set_ui(slack->A[slack->size-1][i], 0, 1);
  mpq_set_si(slack->A[slack->size-1][non_integral], -1, 1);
  mpq_ceiling(slack->B[slack->size-1], temp, slack->temp);
  mpq_neg(slack->B[slack->size-1], slack->B[slack->size-1]);

  ret = branch_and_bound(slack);
  
 end:
  /* Remove changes */
  mpq_clear(temp);

  bring_into_row(slack, slack->size-1, 0, slack->size-1);
  slack->size--;

  return ret;
}

value caml_solve_veclist_simplex(value constraints)
{
  CAMLparam1(constraints);
  CAMLlocal1(list_ptr);
  unsigned int i, j, n, counter;
  int ret;

  if (!simplex_is_initialized) {
    alloc_slack_form(&main_slack, ALLOC_INCREMENT);
    simplex_is_initialized = 1;
  }

  list_ptr = constraints;
  n = Wosize_val(Field(list_ptr, 0))-1;
  n *= 2;

  if (main_slack.allocated_size <= n)
    enlarge_slack_form(&main_slack, n);

  main_slack.size = n;
  main_slack.num_variables = n;

  for (i = 0; i < n; i++)
    ADD_TO_N(main_slack.basic_set, i);
  for (i = 0; i < n; i++)
    mpq_set_ui(main_slack.C[i], 0, 1);

  while (list_ptr != Val_int(0)) {
    if (main_slack.size == main_slack.allocated_size)
      enlarge_slack_form(&main_slack, ALLOC_INCREMENT);
    ADD_TO_B(main_slack.basic_set, main_slack.size);
    mpq_set_str(main_slack.B[main_slack.size], String_val(Field(Field(list_ptr, 0), 0)), 10);
    counter = 1;
    for (j = 0; j < n; j+=2) {
      mpq_set_str(main_slack.A[main_slack.size][j], String_val(Field(Field(list_ptr, 0), counter)), 10);
      mpq_set(main_slack.A[main_slack.size][j+1], main_slack.A[main_slack.size][j]);
      mpq_neg(main_slack.A[main_slack.size][j], main_slack.A[main_slack.size][j]);
      counter++;
    }
    main_slack.size++;
    list_ptr = Field(list_ptr, 1);
  }
  mpq_set_ui(main_slack.V, 0, 1);

  ret = branch_and_bound(&main_slack);

  CAMLreturn(Val_int(ret));
}

/* End of file atsSimplex.c */

