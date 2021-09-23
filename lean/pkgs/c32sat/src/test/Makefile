CFLAGS=-ansi -Wextra -Wall
ADDITIONAL_OBJECTS=../aig_2_cnf_transformation_standard_tseitin.o ../cnf.o ../aig_id_generation.o ../app.o ../memory_management.o ../parser.o ../symbol.o ../error_management.o ../scanner.o ../parse_tree.o ../token.o ../aig.o ../hash_table.o ../parse_tree_analysis.o ../aig_vector.o ../c32sat_math.o ../aig_transformation.o ../sat_solver.o ../linked_list.o ../parse_tree_transformation.o ../config.o ../stack.o
OBJECTS=aig_2_cnf_transformation_standard_tseitin_test.o aig_id_generation_test.o aig_test.o aig_transformation_test.o aig_vector_test.o app_test.o c32sat_math_test.o cnf_test.o error_management_test.o file_comparison.o hash_table_test.o linked_list_test.o memory_management_test.o parse_tree_analysis_test.o parse_tree_test.o parse_tree_transformation_test.o random_utilities.o sat_solver_test.o special_operator.o stack_test.o symbol_test.o test_logging.o test_runner.o token_test.o parser_test.o scanner_test.o ${ADDITIONAL_OBJECTS} ${SATSOLVER_LIB}

all: ${OBJECTS}
	${CC} ${CFLAGS} ${OBJECTS} -o test_runner

aig_2_cnf_transformation_standard_tseitin_test.o: aig_2_cnf_transformation_standard_tseitin_test.h test_logging.h ../cnf.h ../aig.h ../aig_transformation.h ../aig_2_cnf_transformation_standard_tseitin.h ../error_management.h ../memory_management.h 

aig_id_generation_test.o: test_logging.h aig_id_generation_test.h ../aig.h ../aig_id_generation.h ../error_management.h ../memory_management.h 

aig_test.o: aig_test.h test_logging.h ../aig.h ../aig_id_generation.h ../memory_management.h ../error_management.h ../bool.h ../config.h 

aig_transformation_test.o: aig_transformation_test.h test_logging.h ../bool.h ../cnf.h ../aig.h ../aig_transformation.h ../error_management.h ../memory_management.h ../aig_2_cnf_transformation_standard_tseitin.h 

aig_vector_test.o: aig_vector_test.h test_logging.h random_utilities.h special_operator.h ../aig_vector.h ../memory_management.h ../error_management.h ../bool.h ../c32sat_math.h ../config.h 

app_test.o: app_test.h test_logging.h ../exit_codes.h ../app.h ../config.h ../bool.h ../aig.h ../parse_tree_analysis.h ../error_management.h 

c32sat_math_test.o: c32sat_math_test.h test_logging.h ../c32sat_math.h ../config.h ../memory_management.h ../error_management.h 

cnf_test.o: cnf_test.h test_logging.h ../memory_management.h ../error_management.h ../cnf.h ../linked_list.h ../config.h 

error_management_test.o: error_management_test.h test_logging.h ../bool.h ../symbol.h ../token.h ../error_management.h 

file_comparison.o: file_comparison.h 

hash_table_test.o: hash_table_test.h test_logging.h ../hash_table.h ../bool.h ../memory_management.h ../error_management.h 

linked_list_test.o: linked_list_test.h test_logging.h ../bool.h ../linked_list.h ../error_management.h ../memory_management.h 

memory_management_test.o: memory_management_test.h test_logging.h ../memory_management.h ../error_management.h ../token.h ../scanner.h ../parser.h ../parse_tree.h ../aig.h ../bool.h 

parse_tree_analysis_test.o: parse_tree_analysis_test.h test_logging.h ../parse_tree_analysis.h ../memory_management.h ../error_management.h ../scanner.h ../parser.h ../hash_table.h ../parse_tree.h ../linked_list.h ../config.h 

parse_tree_test.o: parse_tree_test.h test_logging.h ../memory_management.h ../error_management.h ../scanner.h ../parser.h ../parse_tree.h ../hash_table.h 

parse_tree_transformation_test.o: parse_tree_transformation_test.h test_logging.h random_utilities.h special_operator.h ../aig.h ../aig_vector.h ../parse_tree.h ../parse_tree_analysis.h ../parse_tree_transformation.h ../memory_management.h ../error_management.h ../scanner.h ../parser.h ../hash_table.h 

random_utilities.o: random_utilities.h 

sat_solver_test.o: sat_solver_test.h test_logging.h ../sat_solver.h ../memory_management.h ../error_management.h 

special_operator.o: special_operator.h ../c32sat_math.h ../bool.h 

stack_test.o: stack_test.h test_logging.h ../memory_management.h ../error_management.h ../stack.h 

symbol_test.o: symbol_test.h test_logging.h ../symbol.h 

test_logging.o: test_logging.h file_comparison.h 

test_runner.o: test_logging.h random_utilities.h c32sat_math_test.h memory_management_test.h token_test.h symbol_test.h error_management_test.h scanner_test.h parser_test.h parse_tree_test.h parse_tree_analysis_test.h app_test.h aig_test.h aig_vector_test.h aig_transformation_test.h linked_list_test.h hash_table_test.h parse_tree_transformation_test.h sat_solver_test.h cnf_test.h stack_test.h aig_id_generation_test.h aig_2_cnf_transformation_standard_tseitin_test.h ../config.h 

token_test.o: token_test.h test_logging.h ../token.h ../memory_management.h 

parser_test.o: parser_test.h test_logging.h ../token.h ../memory_management.h ../error_management.h ../scanner.h ../parser.h ../parse_tree.h 

scanner_test.o: scanner_test.h test_logging.h ../token.h ../memory_management.h ../error_management.h ../scanner.h ../config.h 

clean:
	rm -f *.o test_runner
