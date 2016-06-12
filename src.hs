data Term = Cons String | Var String deriving (Show, Eq)
data Predicate = P String [Term] deriving (Show, Eq)
type Goals = [Predicate]
type Rule = (Predicate, Goals)
data Solution = No | Yes [(Term, Term)] deriving (Show, Eq)


unifyWithHead (P str1 l1) (P str2 l2) = if (str1 == str2) && (checkList list) then Yes list
												else No where (list) = (unifyHelper l1 l2)


checkList [] = True
checkList (x:xs)   | x == (Cons"no", Cons"no") = False
				   | otherwise = checkList xs


unifyHelper [] [] = []
unifyHelper [] _ = [(Cons"no", Cons"no")]
unifyHelper _ [] = []
unifyHelper ((Cons str1):xs) ((Cons str2):ys)   | str1 == str2 = unifyHelper xs ys
												| otherwise = [(Cons"no", Cons"no")]
unifyHelper (x:xs) (y:ys) = (x, y):(unifyHelper xs ys)


allSolutions q kb   | helperAll q kb == [] = functionUnify [q] kb
					| functionList (helperAll q kb) kb == [] && checkConsHead (functionUnify [q] kb) = [Yes (filterConsHead list)]
					| functionList (helperAll q kb) kb /= [] && checkConsHead (functionUnify [q] kb) = [Yes (filterConsHead list3)]
					| otherwise = functionList (helperAll q kb) kb
					 where ([Yes list], [Yes list2], list3) = ((functionUnify [q] kb), (functionList (helperAll q kb) kb), ((filterConsHead list)++list2))


checkConsHead ([Yes list]) = helperConsHead list


helperConsHead [] = False
helperConsHead ((t1, Var _):ts) = helperConsHead ts
helperConsHead ((t1, Cons _):ts) = True


filterConsHead [] = []
filterConsHead ((t1, Cons t):ts) = (t1, Cons t):filterConsHead ts
filterConsHead ((t1, Var _):ts) = filterConsHead ts


functionUnify [] _ = []
functionUnify (x:xs) kb = helperFunUn x kb ++ (functionUnify xs kb)					  				   


first (x:xs) = x


helperFunUn _ [] = []
helperFunUn x ((h, l):rs)   | unifyWithHead x h == No = helperFunUn x rs
							| otherwise = unifyWithHead x h:(helperFunUn x rs)


functionList [] _ = [No]
functionList (q:qs) kb   | functionList qs kb /= [No] && checkDep (q:qs) == True && (filterSol (allSolutions q kb) (functionList qs kb)) /= [] = filterSol (allSolutions q kb) (functionList qs kb)
						 | functionList qs kb /= [No] && checkDep (q:qs) == True && (filterSol (allSolutions q kb) (functionList qs kb)) == [] = filterSol (functionList qs kb) (allSolutions q kb)
						 | functionList qs kb /= [No] && checkDep (q:qs) == False = allSolutions q kb ++ functionList qs kb
						 | otherwise = allSolutions q kb


checkDep [p] = True
checkDep (p1:p2:ps)   | ps == [] = helperCheckDep p1 p2
					  | ps /= [] = helperCheckDep p1 p2 && checkDep ps


helperCheckDep (P str1 l1) (P str2 l2) = helperCheckSol l1 l2


checkSol (Yes []) _ = True
checkSol (Yes l1) (Yes l2)   | length l1 > length l2 = False
							 | otherwise = helperCheckSol l1 l2

helperCheckSol [] [] = True
helperCheckSol [] _ = False
helperCheckSol _ [] = False
helperCheckSol (x:xs) (y:ys)   | x /= y = helperCheckSol (x:xs) ys || helperCheckSol xs (y:ys)
							   | otherwise = True									 

filterSol [] _ = []
filterSol _ [] = []
filterSol (x:xs) list = filter (checkSol x) list ++ filterSol xs list


helperAll q [] = []
helperAll q (x:xs) = helperSol q x ++ helperAll q xs


helperSol q (p, list)   | unifyWithHead q p == No = []
						| list == [] = []
						| otherwise = applySolSubInBody (unifyWithHead q p) list


applySolSubInBody sol [] = []
applySolSubInBody (Yes list1) ((P str list2):ys) = (P str rList):(applySolSubInBody (Yes list1) ys) where (rList) = (helperSub list2 list1)


helperSub _ [] = []
helperSub [] _ = []
helperSub (x:xs) ((y1, y2):ys)   | (check x y2) || (check x y1) = y1:(helperSub xs ys)
								 | otherwise = (helperSub (x:xs) ys) ++ (helperSub xs ((y1, y2):ys))


check (Cons str1) (Cons str2) = str1 == str2
check (Cons str1) (Var str2) = str1 == str2
check (Var str1) (Cons str2) = str1 == str2
check (Var str1) (Var str2) = str1 == str2