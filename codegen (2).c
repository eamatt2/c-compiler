#include <stdio.h>

#include "codegen.h"
#include "table.h"

FILE *codegenout;  // the output of code generation

#define PUSH(arg1) fprintf(codegenout,  "\tpush\t%s\n", arg1 )
#define POP(arg1) fprintf(codegenout,  "\tpop\t%s\n", arg1 )
#define MOV(arg1, arg2) fprintf(codegenout, "\tmov\t%s, %s\n", arg1, arg2)
#define MOV_FROM_IMMEDIATE(arg1, arg2) fprintf(codegenout, "\tmov\t$%d, %s\n", arg1, arg2)
#define MOV_FROM_OFFSET(offset, reg) fprintf(codegenout, "\tmov\t-%d(%%rbp), %s\n", offset, reg)
#define MOV_TO_OFFSET(reg, offset) fprintf(codegenout, "\tmov\t%s, -%d(%%rbp)\n", reg, offset)
#define MOV_FROM_GLOBAL(reg, global) fprintf(codegenout, "\tmov\t%s(%%rip), %s\n", global, reg)
#define MOV_TO_GLOBAL(reg, global) fprintf(codegenout, "\tmov\t%s, %s(%%rip)\n", reg, global)
#define ADD(arg1, arg2) fprintf(codegenout, "\tadd\t%s, %s\n", arg1, arg2)
#define SUB(arg1, arg2) fprintf(codegenout, "\tsub\t%s, %s\n", arg1, arg2)
#define SUBCONST(arg1, arg2) fprintf(codegenout, "\tsub\t$%d, %s\n", arg1, arg2)
#define IMUL(arg1, arg2) fprintf(codegenout, "\timul\t%s, %s\n", arg1, arg2)
#define CDQ() fprintf(codegenout, "\tcdq\n")
#define IDIV(reg) fprintf(codegenout, "\tidiv\t%s\n", reg)
#define CALL(arg1) fprintf(codegenout, "\tcall\t%s\n", arg1)
#define RET fprintf(codegenout, "\tret\n")
#define COMMENT(arg1) fprintf(codegenout, "\t# %s\n", arg1)

#define CMP0(arg) fprintf(codegenout,"\tcmp $0, %s\n", arg)
#define CMP(arg1, arg2) fprintf(codegenout,"\tcmp %s, %s\n", arg1, arg2)
#define JE(labelnum) fprintf(codegenout,"\tje .L%d\n", labelnum)
#define JL(labelnum) fprintf(codegenout,"\tjl .L%d\n", labelnum)
#define JLE(labelnum) fprintf(codegenout,"\tjle .L%d\n", labelnum)
#define JG(labelnum) fprintf(codegenout,"\tjg .L%d\n", labelnum)
#define JGE(labelnum) fprintf(codegenout,"\tjge .L%d\n", labelnum)
#define JMP(labelnum) fprintf(codegenout,"\tjmp .L%d\n", labelnum)
#define LABEL(labelnum) fprintf(codegenout,".L%d:\n", labelnum)

#define JNE(labelnum) fprintf(codegenout,"\tjne .L%d\n", labelnum)

const string const param_registers[] = { "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"}; // all const

static void codegen_main(T_main main);

static void codegen_decllist(T_decllist decllist);

static void codegen_stmtlist(T_stmtlist stmtlist);

static void codegen_funclist(T_funclist funclist);

static void codegen_func(T_func func);

static void codegen_stmtlist(T_stmtlist stmtlist);

static void codegen_stmt(T_stmt stmt);

static void codegen_assignstmt(T_stmt stmt);

static void codegen_ifstmt(T_stmt stmt);

static void codegen_ifelsestmt(T_stmt stmt);

static void codegen_whilestmt(T_stmt stmt);

static void codegen_compoundstmt(T_stmt stmt);

static void codegen_expr(T_expr expr);

static void codegen_identexpr(T_expr expr);

static void codegen_callexpr(T_expr expr);

static void codegen_intexpr(T_expr expr);

static void codegen_charexpr(T_expr expr);

static void codegen_strexpr(T_expr expr);

static void codegen_arrayexpr(T_expr expr);

static void codegen_unaryexpr(T_expr expr);

static void codegen_binaryexpr(T_expr expr);

static void codegen_castexpr(T_expr expr);

static void emit_prologue(int size);

static void emit_epilogue();

static int bitwidth(T_type type);

typedef struct S_offset_scope *T_offset_scope;

int labelCounter = 0;

struct S_offset_scope {
  T_table table;
  int stack_size;
  int current_offset;
  T_offset_scope parent;
};

static T_offset_scope create_offset_scope(T_offset_scope parent) {
  T_offset_scope offset_scope = xmalloc(sizeof(*offset_scope));
  offset_scope->table = create_table();
  // start after the dynamic link to the caller's %rbp
  offset_scope->current_offset = 8;
  offset_scope->stack_size = 0;
  offset_scope->parent = parent;
  return offset_scope;
}

static T_offset_scope destroy_offset_scope(T_offset_scope offset_scope) {
  T_offset_scope parent_offset_scope = offset_scope->parent;
  destroy_table(offset_scope->table);
  free(offset_scope);
  return parent_offset_scope;
}

struct S_offset {
  int offset;
};

typedef struct S_offset * T_offset;

static T_table global_symbols;

static T_offset_scope current_offset_scope;

void insert_offset(T_offset_scope scope, string ident, int size) {
  T_offset entry = xmalloc(sizeof(*entry));
  entry->offset = scope->current_offset;
  insert(scope->table, ident, (void*) entry);
  scope->stack_size += size;
  scope->current_offset += size;
}

static int lookup_offset_in_scope(T_offset_scope offset_scope, string ident) {
  T_offset offset = (T_offset) lookup(offset_scope->table, ident);
  if (NULL == offset) {
    fprintf(stderr, "FATAL: symbol not in table.  double-check the code that inserts the symbol into the offset scope.");
  }
  return offset->offset;
}

static T_offset lookup_offset_in_all_offset_scopes(T_offset_scope offset_scope, string ident) {
  // loop over each offset_scope and check for a binding for ident
  while (NULL != offset_scope) {
    // check for a binding in this offset_scope
    T_offset offset = (T_offset) lookup(offset_scope->table, ident);
    if (NULL != offset) {
      return offset;
    }
    // no binding in this offset_scope, so check the parent
    offset_scope = offset_scope->parent;
  }
  // found no binding in any offset_scope
  return NULL;
}

void codegen(T_prog prog) {
  // no need to record symbols in the global offset_scope.  the assembler and linker handle them.
  current_offset_scope = NULL;
  
  // emit assembly header
  fprintf(codegenout, ".file \"stdin\"\n");
  
  // emit a .comm for global vars
  global_symbols = create_table();
  // loop over each global symbol.  emit .comm and add to global symtab
  T_decllist decllist = prog->decllist;
  while (NULL != decllist) {
    if (E_functiontype != decllist->decl->type->kind) {
      fprintf(codegenout, ".comm\t%s,%d\n", decllist->decl->ident, bitwidth(decllist->decl->type));
      insert(global_symbols, decllist->decl->ident, decllist->decl->ident);
    }
    decllist = decllist->tail;
  }

  // optional: emit an .rodata section and label for strings

  // go through each function
  codegen_funclist(prog->funclist);

  // generate the code for main
  codegen_main(prog->main);

  // free the global symbol table
  free(global_symbols);
}

static void codegen_main(T_main main) {
  // create a new scope
  current_offset_scope = create_offset_scope(NULL);

  // emit the pseudo ops for the function definition
  fprintf(codegenout, ".text\n");
  fprintf(codegenout, ".globl %s\n", "main");
  fprintf(codegenout, ".type %s, @function\n", "main");

  // emit a label for the function
  fprintf(codegenout, "%s:\n", "main");

  // add local declarations to the scope
  codegen_decllist(main->decllist);

  COMMENT("stack space for argc and argv");
  insert_offset(current_offset_scope, "argc", 8);  // int argc
  insert_offset(current_offset_scope, "argv", 8);  // char **argv

  COMMENT("emit main's prologue");
  emit_prologue(current_offset_scope->stack_size);

  COMMENT("move argc and argv from parameter registers to the stack");
  int offset;
  offset = lookup_offset_in_scope(current_offset_scope, "argc");
  MOV_TO_OFFSET("%rdi", offset);
  offset = lookup_offset_in_scope(current_offset_scope, "argv");
  MOV_TO_OFFSET("%rsi", offset);
  
  COMMENT("generate code for the body");
  codegen_stmtlist(main->stmtlist);

  COMMENT("generate code for the return expression");
  codegen_expr(main->returnexpr);
  COMMENT("save the return expression into %rax per the abi");
  POP("%rax");

  COMMENT("emit main's epilogue");
  emit_epilogue();

  // exit the scope
  current_offset_scope = destroy_offset_scope(current_offset_scope);
}

static void codegen_funclist(T_funclist funclist) {
  while (NULL != funclist) {
    codegen_func(funclist->func);
    funclist = funclist->tail;
  }
}

static void codegen_func(T_func func) {
  //create new scope for function
  current_offset_scope = create_offset_scope(current_offset_scope);
  
  //emit the pseudo ops for the function definition
  fprintf(codegenout, ".text\n");
  fprintf(codegenout, ".globl %s\n", func->ident);
  fprintf(codegenout, ".type %s, @function\n", func->ident);

  //emit a label for the function, which is name followed by colon
  fprintf(codegenout, "%s:\n", func->ident);

  //inserting offsets into the symbol table
  //(for this simplified project, can always assume there is just one parameter in paramlist)
  insert_offset(current_offset_scope, func->paramlist->ident, 8);

  //add local declarations to the scope, by calling codegen_decllist
  codegen_decllist(func->decllist);

  //emit the prologue function with stack size
  emit_prologue(current_offset_scope->stack_size);

  //copying parameters to memory
  int offset = lookup_offset_in_scope(current_offset_scope, func->paramlist->ident);
  MOV_TO_OFFSET("%rdi", offset);

  //generate code for the body of the function using its statement list.
  codegen_stmtlist(func->stmtlist);

  //generate code for return expression, generate code to retrieve the value that the expression generator pushes onto the stack
  codegen_expr(func->returnexpr);
  POP("%rax");

  //emit epilogue
  emit_epilogue();

  //destroy function's scope
  current_offset_scope = destroy_offset_scope(current_offset_scope);
}

static void codegen_decllist(T_decllist decllist) {
  //if scope isn't null, loop through list to insert each element into offset scope
  //if(current_offset_scope != NULL) {
    while(decllist != NULL) {
      insert_offset(current_offset_scope, decllist->decl->ident, 8);
      decllist = decllist->tail; //increment through list
    }
  //}
}

/* statements */
static void codegen_stmtlist(T_stmtlist stmtlist) {
  while (NULL != stmtlist) {
    codegen_stmt(stmtlist->stmt);
    stmtlist = stmtlist->tail;
  }
}

static void codegen_stmt(T_stmt stmt) {
  if (NULL == stmt) {
    fprintf(stderr, "FATAL: stmt is NULL in codegen_stmt\n");
    exit(1);
  }
  switch (stmt->kind) {
  case E_assignstmt: codegen_assignstmt(stmt); break;
  case E_ifstmt: codegen_ifstmt(stmt); break;
  case E_ifelsestmt: codegen_ifelsestmt(stmt); break;
  case E_whilestmt: codegen_whilestmt(stmt); break;
  case E_compoundstmt: codegen_compoundstmt(stmt); break;
  default: fprintf(stderr, "FATAL: unexpected stmt kind in codegen_stmt\n"); exit(1); break;
  }
}



static void codegen_assignstmt(T_stmt stmt) {
  COMMENT("entering assignstmt");

  if(stmt->assignstmt.left->kind == E_unaryexpr) {
    // Handle dereferenced pointer
    // Generate code for the pointer expression (computes the address)
    codegen_expr(stmt->assignstmt.left->unaryexpr.expr);

    codegen_expr(stmt->assignstmt.right);

    POP("%rax");
    // Pop the address into %rbx
    POP("%rbx");
    // Move the RHS value into the address pointed by %rbx
    MOV("%rax", "(%rbx)");
  }

  else {
     codegen_expr(stmt->assignstmt.right);
     POP("%rax");
    // Handle identifier (simple variable)
    // Look up the variable's offset in the current scope
    int offset = lookup_offset_in_scope(current_offset_scope, stmt->assignstmt.left-> identexpr);    // Move the RHS value into the variable's location on the stack
    MOV_TO_OFFSET("%rax", offset);
  }

      //default:
        //  fprintf(stderr, "Unsupported LHS expression type in assignment\n");
          //exit(1);
}

static void codegen_ifstmt(T_stmt stmt) {
  COMMENT("entering ifstmt");
  int jump = labelCounter++;
  //evaluate the condition
  codegen_expr(stmt->ifstmt.cond);

  //store result in %rax
  POP("%rax");
  //compare to "false"
  CMP("$0", "%rax");
  //jump only if false
  JE(jump);

  //evaluate the body only if condition is true
  codegen_stmt(stmt->ifstmt.body);
  LABEL(jump);
}

static void codegen_ifelsestmt(T_stmt stmt) {
  COMMENT("entering ifelsestmt");
  int elseLabel = labelCounter++;
  int endLabel = labelCounter++;
  //evaluate the condition expression
  codegen_expr(stmt->ifelsestmt.cond);

  //store result in %rax
  POP("%rax");
  //compare to "false"
  CMP("$0", "%rax");
  //jump only if false to else branch
  JE(elseLabel);

  //contents of if branch
  codegen_stmt(stmt->ifelsestmt.ifbranch);
  //unconditionally ump past else branch
  JMP(endLabel);

  LABEL(elseLabel);
  //contents of else branch
    codegen_stmt(stmt->ifelsestmt.elsebranch);

  LABEL(endLabel);
}

static void codegen_whilestmt(T_stmt stmt) {
  COMMENT("entering whilestmt");
  int head = labelCounter++;
  int endLabel = labelCounter++;
  //head of loop
  LABEL(head);
  //evaluate the condition expression
  codegen_expr(stmt->whilestmt.cond);

  //store result in %rax
  PUSH("%rax");
  //compare to "false"
  CMP("$0", "%rax");
  //jump only if false
  JE(endLabel);
  
  //contents of the while body
  codegen_stmt(stmt->whilestmt.body);
  //unconditionally jump to loop head
  JMP(head);
  LABEL(endLabel);
}

static void codegen_compoundstmt(T_stmt stmt) {
  COMMENT("entering compound");
  //generate code for body of compound statement
  codegen_stmtlist(stmt->compoundstmt.stmtlist);
}

/* expressions */
static void codegen_expr(T_expr expr) {
  if (NULL == expr) {
    fprintf(stderr, "FATAL: unexpected NULL in codegen_expr\n");
    exit(1);
  }
  switch (expr->kind) {
  case E_identexpr: codegen_identexpr(expr); break;
  case E_callexpr: codegen_callexpr(expr); break;
  case E_intexpr: codegen_intexpr(expr); break;
  case E_charexpr: codegen_charexpr(expr); break;
  case E_strexpr: codegen_strexpr(expr); break;
  case E_arrayexpr: codegen_arrayexpr(expr); break;
  case E_unaryexpr: codegen_unaryexpr(expr); break;
  case E_binaryexpr: codegen_binaryexpr(expr); break;
  case E_castexpr: codegen_castexpr(expr); break;
  default: fprintf(stderr, "FATAL: unexpected expr kind in codegen_expr\n"); exit(1); break;
  }
}

static void codegen_identexpr(T_expr expr) {
  // todo: given in class
  //look up the ident, then move it to an intermidate register
  int offset = lookup_offset_in_scope(current_offset_scope, expr->identexpr);
  MOV_FROM_OFFSET(offset, "%rax");
  PUSH("%rax");
}

static void codegen_callexpr(T_expr expr) {
  COMMENT("entering callexpr");
  //generate code for parameter's expression
  codegen_expr(expr->callexpr.args->expr);
  POP("%rdi"); //pop %rax to pass through parameter
  COMMENT("call instruction to function's identifier");
  CALL(expr->callexpr.ident); //emit call instruction to function's identifier
  PUSH("%rax"); //push return value back to stack
}

static void codegen_intexpr(T_expr expr) {
  //move immediate value into a register and push onto stack
  MOV_FROM_IMMEDIATE((int)expr->intexpr, "%rax");
  PUSH("%rax");
}

static void codegen_charexpr(T_expr expr) {
  COMMENT("push the character");
  MOV_FROM_IMMEDIATE((int) expr->charexpr, "%rax");
  PUSH("%rax");
}

static void codegen_strexpr(T_expr expr) {
  // bonus exercise
}

static void codegen_arrayexpr(T_expr expr) {
  // bonus exercise
}

static void codegen_unaryexpr(T_expr expr) {
  //(3 cases: &, *, !)
  switch(expr->unaryexpr.op) {
    case E_op_ref:
      COMMENT("doing ref");
      if(expr->unaryexpr.expr->kind == E_identexpr) {
        MOV("%rbp", "%rax");
        int offset = lookup_offset_in_scope(current_offset_scope, expr->unaryexpr.expr->identexpr);
        SUBCONST(offset, "%rax");
        PUSH("%rax");
      }
      break;
    case E_op_deref:
      COMMENT("doing deref");
      codegen_expr(expr->unaryexpr.expr);
      POP("%rax");
      MOV("(%rax)", "%rbx");
      PUSH("%rbx");
      break;
    case E_op_not:
      COMMENT("doing not");
      int l0 = labelCounter++;
      codegen_expr(expr->unaryexpr.expr);
      POP("%rax");
      CMP("$0", "%rax");
      MOV_FROM_IMMEDIATE(1, "%rax");
      JE(l0);
      MOV_FROM_IMMEDIATE(0, "%rax");
      LABEL(l0);
      PUSH("%rax");
      break;
  }

  //PUSH("%rax");  
}

static void codegen_binaryexpr(T_expr expr) {
  //generate code for left and right operands of expression
  codegen_expr(expr->binaryexpr.left);
  codegen_expr(expr->binaryexpr.right);

  //pop left and right results of operand
  POP("%rbx"); //right
  POP("%rax"); //left
  
  //switch case to compute result of current expression
  //project 4: added cases for && and ||
  switch (expr->binaryexpr.op) {
    case E_op_plus: ADD("%rbx", "%rax"); break;
    case E_op_minus: SUB("%rbx", "%rax"); break;
    case E_op_times: IMUL("%rbx", "%rax"); break;
    case E_op_divide: CDQ(); IDIV("%rbx"); break;
    case E_op_mod: CDQ(); IDIV("%rbx"); MOV("%rdx", "%rax"); break;
    case E_op_and:
      COMMENT("doing and");
      int jump1 = labelCounter++, jump2 = labelCounter++;
      CMP("$0", "%rax"); //test left operand
      JE(jump1); //jump only if false
      CMP("$0", "%rbx"); //test right operand
      JE(jump1); //jump only if false
      MOV_FROM_IMMEDIATE(1, "%rax"); //set result %rax to true
      JMP(jump2);
      LABEL(jump1);
      MOV_FROM_IMMEDIATE(0, "%rax"); //set result %rax to false
      LABEL(jump2); //save result of expression, push onto stack
      PUSH("%rax");
      break;
    case E_op_or:
      COMMENT("doing or");
      int j1 = labelCounter++, j2 = labelCounter++;
      CMP("$0", "%rax"); //test left operand
      JNE(j1); //jump only if NOT false
      CMP("$0", "%rbx"); //test right operand
      JNE(j1); //jump only if NOT false
      MOV_FROM_IMMEDIATE(0, "%rax"); //set result %rax to false
      JMP(j2);
      LABEL(j1);
      MOV_FROM_IMMEDIATE(1, "%rax"); //set result %rax to true
      LABEL(j2);
      PUSH("%rax");
      break;

    case E_op_lt:
      int firstLabel = labelCounter++;
      int secondLabel = labelCounter++;
      COMMENT("Do the less than");
      COMMENT("Compare left operand with right operand");
      CMP("%rbx", "%rax");
      COMMENT("Jump to first label if operand1 is less than operand2");
      JL(firstLabel);
      MOV_FROM_IMMEDIATE(0, "%rax");
      JMP(secondLabel);

      LABEL(firstLabel);
      MOV_FROM_IMMEDIATE(1, "%rax");
      LABEL(secondLabel);
      break;

    default:
        fprintf(stderr, "Operator not supported: %d\n", expr->binaryexpr.op);
        break;
    }

  PUSH("%rax"); //push result to stack
}

static void codegen_castexpr(T_expr expr) {
  // bonus: truncate or extend data between bitwidths depending on type  
  codegen_expr(expr->castexpr.expr);
}

/**
 * Emit a function prologue, given some size in bytes of the local
 * variables in the stack frame.
 */
static void emit_prologue(int size) {
	//save stack
	PUSH("%rbp");
	MOV("%rsp", "%rbp");
	if (size > 0) {
		SUBCONST(size, "%rsp");
	}
	PUSH("%rbx");
}

static void emit_epilogue() {
	POP("%rbx");
	MOV("%rbp", "%rsp");
	POP("%rbp");
	RET;
}

/**
 * This function returns the size of a type in bytes.
 */
static int bitwidth(T_type type) {
  switch (type->kind) {
  case E_primitivetype:
    switch (type->primitivetype) {
    case E_typename_int:
      // 32-bit integers
      return 4;
    case E_typename_char:
      // characters are 1 byte
      return 1;
    default:
      fprintf(stderr, "FATAL: unexpected kind in compare_types\n");
      exit(1);
    }
    break;
  case E_pointertype:
    // pointers are to 64-bit addresses
    return 8;
  case E_arraytype:
    // arrays are the size times the bitwidth of the type
    return type->arraytype.size * bitwidth(type->arraytype.type);
  case E_functiontype:
    fprintf(stderr, "FATAL: functions as values are not supported\n");
    exit(1);
    break;
  default:
    fprintf(stderr, "FATAL: unexpected kind in bitwidth\n");
    exit(1);
    break;
  }  
}
