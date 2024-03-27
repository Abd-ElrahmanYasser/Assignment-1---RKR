import re
import time

class LogicalOperations:
    @staticmethod
    def eliminate_implication(expression):
        pattern = r'\(*(.*)\s*\-\>\s*(.*)\)*'
        while re.search(pattern, expression) is not None:
            match = re.search(pattern, expression).group(0)
            var1 = re.search(pattern, expression).group(1).strip()
            var2 = re.search(pattern, expression).group(2).strip()
            expression = expression.replace(match, f'(~{var1} ∨ {var2}')

        return expression

    @staticmethod
    def apply_demorgan_law(expression):
        pattern = r"\~\((.*)\s*([∨∧])\s*(.*)\)"
        while re.search(pattern, expression) is not None:
            match = re.search(pattern, expression).group(0)
            var1 = re.search(pattern, expression).group(1).strip()
            var2 = re.search(pattern, expression).group(3).strip()
            symbol = re.search(pattern, expression).group(2).strip()
            if symbol == '∨':
                expression = expression.replace(match, f'~{var1} ∧ ~{var2}')
            else:
                expression = expression.replace(match, f'~{var1} ∨ ~{var2}')

        return expression

    @staticmethod
    def remove_double_negation(expression):
        pattern = r'\~\~(.*)'
        while re.search(pattern, expression) is not None:
            match = re.search(pattern, expression).group(0)
            var = re.search(pattern, expression).group(1).strip()
            expression = expression.replace(match, var)

        return expression
    
    @staticmethod
    def standardize_variable(expression, start_index):
        standardized_predicates = []
        index = start_index
        
        predicates = expression.split(' ∨ ')
        for predicate in predicates:
            quantifier, rest = predicate[0], predicate[1:]
            var, expr = rest.split('P' if 'P' in rest else 'R')
            var = var.strip()
            expr = expr.strip()
            if quantifier == '∀':
                # Universal quantification
                standardized_expr = f"∀{var}{index}P({var}{index})"
            elif quantifier == '∃':
                # Existential quantification
                standardized_expr = f"∃{var}{index}R({var}{index})"
            else:
                # Handle error
                raise ValueError("Invalid quantifier")

            standardized_predicates.append(standardized_expr)
            index += 1

        return ' ∨ '.join(standardized_predicates)

    @staticmethod
    def convert_to_prenex_form(expression):
        quantifier_pattern = r"(\∀|\∃)([a-zA-Z]+)" # Detects ∀ and ∃ quantifiers
        quantifiers = re.findall(quantifier_pattern, expression) # Finds all quantifiers in the expression
        
        # Separate the quantified part from the rest of the formula
        quantified_part = ""
        rest_of_formula = expression
        
        # Remove quantifiers from the formula
        for quantifier in quantifiers:
            quantified_part += quantifier[0] + quantifier[1] + "("
            rest_of_formula = rest_of_formula.replace(quantifier[0].strip() + quantifier[1].strip(), "")

        # Close the quantified part
        quantified_part += rest_of_formula + ")" * len(quantifiers)
            
        # remove extra spaces
        return quantified_part.replace("  ", " ")
    
    @staticmethod
    def eliminate_quantifiers(experation):
        parts = experation.split(' ')
        new_list1 = []

        for part in parts:
            if part.startswith(('∀', '∃')):
                continue
            else:
                new_list1.append(part)
        new_list2 = ' '.join(new_list1)
        return new_list2

    @staticmethod
    def skolemization(expression):
        # Regular expression pattern to match existential quantifiers and variables
        quantifier_pattern = r"(∀|∃)([a-zA-Z]+)"

        # Find all existential quantifiers in the formula
        quantifiers = re.findall(quantifier_pattern, expression)

        # Replace each existential quantifier with a Skolem function
        skolemized_formula = expression
        
        for quantifier in quantifiers:
            if quantifier[0] == '∃':
                temp = re.search(r"∀([a-zA-Z]+)", expression)
                if any(q[0] == '∀' for q in quantifiers): 
                    temp = temp.group(1)
                    skolem_function = "F(" + temp + ")"
                else:
                    skolem_function = "C"
                    temp = ""
                skolemized_formula = re.sub(quantifier[1], skolem_function, skolemized_formula)
                skolemized_formula = skolemized_formula.replace(quantifier[0].strip() + skolem_function[0].strip() + "(".strip() + temp.strip() + ")".strip(), "")
                if any(q[0] == '∃' for q in skolemized_formula):
                    skolemized_formula = skolemized_formula.replace("∃".strip() + re.search(r"∃([a-zA-Z]+)", skolemized_formula).group(1).strip(), "")
                break

        return skolemized_formula.replace("  ", " ")
        
    @staticmethod
    def convert_to_cnf(expression): 
        # A | F(x) ∨∧ (A | F(x) ∨∧ A | F(x))
        pattern = r'(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))\s*[∨∧]\s*\((?:(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))\s*[∨∧]\s*(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\))))\)'
        formulas = re.findall(pattern, expression)
        if len(formulas) > 0:
            for formula in formulas:
                original_formula = formula
                
                temp = re.search(r'(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))', formula).group(0)
                expr1 = "(".strip() + temp
                expr2 = "(".strip() + temp
                
                formula = formula.replace(temp, "")
                
                symbol = re.search(r'[∨∧]', formula).group(0)
                expr1 += " " + symbol + " "
                expr2 += " " + symbol + " "
                
                formula = formula.replace(symbol, "")
                
                temp = re.search(r'(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))', formula).group(0)
                expr1 += temp + ")".strip()
                
                formula = formula.replace(temp, "")
                
                temp = re.search(r'(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))', formula).group(0)
                expr2 += temp + ")".strip()
                
                symbol = re.search(r'[∨∧]', formula).group(0)

                expression = expression.replace(original_formula, f'{expr1} {symbol} {expr2}') 
          
        # (A | F(x) ∧ A | F(x)) ∨ (A | F(x) ∧ A | F(x))
        pattern = r'\((?:(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))\s*\∧\s*(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\))))\)'
        formulas = re.findall(pattern, expression)
        
        if len(formulas) > 0:
            terms = []
            for formula in formulas:
                pattern = r'(?:[a-zA-Z]|(?:[a-zA-Z]\s*\(.*?\)))'
                terms.extend(re.findall(pattern, formula))
            expr = ""
            n = int(len(terms) / len(formulas))
            for i in range(n):
                for j in range(n):
                    if (i + j < len(terms)):
                        expr += f'({terms[i]} ∨ {terms[j+n]})'
                        if j < n-1:
                            expr += " ∧ "
                if i < n-1:
                    expr += " ∧ "
            cumulative_formula = ""
            for formula in formulas:
                cumulative_formula += formula
            cumulative_formula = cumulative_formula.replace(")(", ") ∨ (").strip()
            expression = expression.replace(cumulative_formula, expr)          
            
        return expression
    
    @staticmethod
    def convert_to_clauses(expression):
        clauses = re.split(r'∧', expression)
        clauses = [clause.strip() for clause in clauses]
        
        return clauses
    
    @staticmethod
    def rename_variables(clauses):
        var_pattern = r'[a-zA-Z]\(([a-zA-Z]*?)\)' 
        variables = re.findall(var_pattern, clauses)
        variable_map = {}
        
        for v in variables:
            if v not in variable_map:
                variable_map[v] = 1
            else:
                variable_map[v] += 1
            var_pos = "(".strip() + v.strip()
            clauses = clauses.replace(var_pos + ")".strip(), var_pos + str(variable_map[v]).strip()+ ")".strip(), 1)
            
        return clauses
        
        
if __name__ == "__main__":
    operation = LogicalOperations()
    
    while True:
        print("1. Eliminate Implication")
        print("2. Apply DeMorgan's Law")
        print("3. Remove Double Negation")
        print("4. Standardize Variable")
        print("5. Convert to Prenex Form")
        print("6. Skolemization")
        print("7. Eliminate Universal Quantifiers")
        print("8. Convert to CNF")
        print("9. Turn Conjunctions into Clauses")
        print("10. Rename Variables in Clauses")
        print("0. Exit\n")
        num = int(input("Please enter a number from 0 to 10 to apply the functions: "))
        print()
        
        match num:
            case 1:
                expression = '(P -> Q)'
                print("Original String : ", expression)
                print("String after applying the implication : ", operation.eliminate_implication(expression))
            case 2:
                expression1 = '~(P ∨ Q)'
                expression2 = '~(P ∧ Q)'
                print("String Before Applying Demorgan : ", expression1)
                print("String After Applying DeMorgan : ", operation.apply_demorgan_law(expression1))
                print("String Before Applying Demorgan : ", expression2)
                print("String After Applying DeMorgan : ", operation.apply_demorgan_law(expression2))
            case 3:
                expression = '~~P ∨ Q'
                print("Orignal String", expression)
                print("After Applying Double Negation : ", operation.remove_double_negation(expression))
            case 4:
                expression = '∀xP(x) ∨ ∃xR(y)'
                print("Original String", expression)
                start_index = 1
                print("After Applying Standardization : ",operation.standardize_variable(expression, start_index))
            case 5:
                expr = "A ∨ ∀x F(x)"
                print("\nPrenex form: \nEx.1: A ∨ ∀x F(x)  → ", operation.convert_to_prenex_form(expr))
                expr = "∃x(P(x)) ∧ ∀x(P(x))"
                print("Ex.2: ∃x(P(x)) ∧ ∀x(P(x))  → ", operation.convert_to_prenex_form(expr))
            case 6:
                expr = "∀x ∃y P(x) ∨ Q(y)"
                print("\nskolemization: \n∀x ∃y P(x) ∨ Q(y)  → ", operation.skolemization(expr))
            case 7:
                expression1 = "∀x P(x, y) → Q(x)"
                expression2 = "∃y P(x, y) → Q(x)"
                print("Original String : ", expression1)
                print("After Remove Universal Quantifier ", operation.eliminate_quantifiers(expression1))
                print("Original String : ", (expression2))
                print("After Remove Universal Quantifier ", operation.eliminate_quantifiers(expression2))
            case 8:
                expr = "p ∨ (q ∧ r)"
                print("\nCNF: \nEx.1: p ∨ (q ∨ r)  → ", operation.convert_to_cnf(expr))
                expr = "(p ∧ s) ∨ (q ∧ r)"
                print("Ex.2: (p ∧ s) ∨ (q ∧ r)  → ", operation.convert_to_cnf(expr))                   
            case 9:
                expr = "(p ∨ q) ∧ (p ∨ r) ∧ (s ∨ q) ∧ (s ∨ r)"
                print("\nClauses: \n(p ∨ q) ∧ (p ∨ r) ∧ (s ∨ q) ∧ (s ∨ r)  → ", operation.convert_to_clauses(expr))
            case 10:
                expr = "p(x) ∨ q(y) ∨ k(x)"
                print("\nRename Variables: \np(x) ∨ q(y) ∨ k(x)  → ", operation.rename_variables(expr))
            case 0:
                break
            case _:
                print("Please enter a valid number")
        print() 
        time.sleep(5)

        