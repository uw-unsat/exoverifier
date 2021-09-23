OBJECTS=aig.o aig_2_cnf_transformation_standard_tseitin.o aig_id_generation.o aig_transformation.o aig_vector.o app.o c32sat.o c32sat_math.o cnf.o config.o error_management.o hash_table.o linked_list.o memory_management.o parse_tree.o parse_tree_analysis.o parse_tree_transformation.o token.o parser.o sat_solver.o stack.o symbol.o scanner.o ${SATSOLVER_LIB}

all: ${OBJECTS}
	${CC} ${CFLAGS} ${OBJECTS} -o ../c32sat

aig.o: aig.h aig_id_generation.h bool.h memory_management.h error_management.h c32sat_math.h config.h stack.h hash_table.h 

aig_2_cnf_transformation_standard_tseitin.o: aig.h cnf.h hash_table.h stack.h aig_id_generation.h aig_2_cnf_transformation_standard_tseitin.h 

aig_id_generation.o: aig_id_generation.h aig.h bool.h hash_table.h stack.h 

aig_transformation.o: aig_transformation.h aig.h memory_management.h cnf.h aig_2_cnf_transformation_standard_tseitin.h 

aig_vector.o: aig.h aig_vector.h c32sat_math.h memory_management.h config.h 

app.o: exit_codes.h app.h bool.h config.h c32sat_math.h sat_solver.h cnf.h memory_management.h error_management.h scanner.h parser.h parse_tree.h parse_tree_analysis.h aig.h aig_vector.h aig_id_generation.h aig_transformation.h hash_table.h parse_tree_transformation.h linked_list.h 

c32sat.o: app.h 

c32sat_math.o: c32sat_math.h bool.h config.h memory_management.h 

cnf.o: cnf.h memory_management.h error_management.h linked_list.h bool.h c32sat_math.h config.h 

config.o: config.h bool.h 

error_management.o: error_management.h bool.h symbol.h token.h config.h scanner.h 

hash_table.o: hash_table.h bool.h memory_management.h c32sat_math.h 

linked_list.o: linked_list.h bool.h memory_management.h 

memory_management.o: exit_codes.h bool.h c32sat_math.h memory_management.h error_management.h 

parse_tree.o: bool.h stack.h parse_tree.h symbol.h memory_management.h 

parse_tree_analysis.o: config.h bool.h parse_tree_analysis.h parse_tree.h hash_table.h linked_list.h memory_management.h error_management.h stack.h 

parse_tree_transformation.o: memory_management.h parse_tree_transformation.h aig.h aig_vector.h hash_table.h parse_tree.h parse_tree_analysis.h config.h stack.h bool.h 

token.o: memory_management.h token.h bool.h 

parser.o: token.h symbol.h memory_management.h error_management.h scanner.h parser.h parse_tree.h 

sat_solver.o: sat_solver.h memory_management.h ${SATSOLVER_HEADER}

stack.o: memory_management.h stack.h 

symbol.o: symbol.h token.h parse_tree.h 

scanner.o: token.h error_management.h scanner.h bool.h memory_management.h c32sat_math.h config.h 

clean:
	rm -f *.o c32sat sat_solver.c
