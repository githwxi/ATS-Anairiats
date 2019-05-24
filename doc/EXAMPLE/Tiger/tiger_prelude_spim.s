	.text
.globl main
main:
	addi $sp, $sp, -4
	sw $fp, 0($sp)
	move $fp, $sp
	addi $sp, $sp, -4
	sw $ra, -4($fp)
	jal tiger_main
	lw $ra, -4($fp)
	move $sp, $fp
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
	#end of [main]

	.text
.globl tiger_flush
tiger_flush:
	jr $ra
	#end of [tiger_flush]

	.text
.globl tiger_print
tiger_print:
	li $v0, 4 # print a string
	syscall
	jr $ra
	#end of [tiger_print]

	.text
.globl tiger_print_int
tiger_print_int:
	li $v0, 1 # print an integer
	syscall
	jr $ra
	#end of [tiger_print_int]

	.text
.globl tiger_array_alloc
tiger_array_alloc:
	li $a1, 4
	mul $a0, $a0, $a1
	li $v0, 9 # sbrk
	syscall
	jr $ra
	#end of [tiger_array_alloc]

	.text
.globl tiger_array_init
tiger_array_init:
	addi $sp, $sp, -4
	sw $fp, 0($sp)
	move $fp, $sp
	move $v0, $zero
L0_TIGERATS:
	bge $v0, $a1, L2_TIGERATS
	li $a3, 4
	mul $a3, $v0, $a3
	add $a3, $a0, $a3
	sw $a2, 0($a3)
	addi $v0, $v0, 1
	j L0_TIGERATS
L2_TIGERATS:
	move $v0, $zero
	move $sp, $fp
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
	.text
	# end of [tiger_array_init]
	
	.text
.globl tiger_array_make_elt
tiger_array_make_elt:
	addi $sp, $sp, -4
	sw $fp, 0($sp)
	move $fp, $sp
	addi $sp, $sp, -4
	sw $ra, -4($fp)
	# a0: size; a1:	init
	move $a3, $a0
	li $a2, 4
	mul $a0, $a0, $a2
	li $v0, 9 # sbrk
	syscall
	move $a2, $a1 # init
	move $a1, $a3 # size
	move $a0, $v0 # ptr
	move $v1, $v0 # ptr
	jal tiger_array_init
	move $v0, $v1
	lw $ra, -4($fp)
	move $sp, $fp
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
	# end of [tiger_array_make_elt]

# end of [tigerats_prelude_spim.s]
