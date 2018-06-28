Aliaksei Suvorau 374118

Opis języka Varlang oraz haskell-owej implementacji interpretera dla niego

-- OPIS

	Jeżyk varalang nazywa się tak, ponieważ głównym jego nietypowym mechanizmem jest variant (specjalna struktura).
	Opis variantu - to ciąg rówżnych identyfikatorów oraz opis typów dodatkowych danych dla każdego z tych identyfikatorów.
	Podobny mechanizm jest w jęyju Nianiolang, Perl oraz Haskell.

	varlang: 
	var(A => char, B => int)

	haskell
	data t = A Char | B Int


-- STRUKTURA
	Program w języku varlang jest ciągiem instruckji. Każda instrukcja (nawet deklaracja funkcji albo instrukcje jak for, while, if)
	powinna mieć na końcu średnik (ostatnia instrukcja programu może go nie mieć)

-- Komentarze
	// - jednolinijkowy
	/* 	wielolinijkowy
		wielolinijkowy
	*/

-- INSTRUKCJE
	varlang obsługuje większość standardowych instrukcji dla operacji matematycznych na int-ach (--, ++, +, += ...) oraz bool-owe (!, &&, || ...). Zachowanie tych instrukcji jest takie same jak w C-podobnych językach.

	Ma także standardowe instrukcje : while , if, if .. else, for (o nim niżej)


-- INSTRUKCJE DLA VARIANTÓW
	Warianty obsługują się za pomocą specjalnych instrukcji "match" oraz "is".

	-- match
		sprawdzenie różnych możliwych opcji dla variantu
		przykład:
			var(a => int, b => dict(int, int)) testVar1, testVar2;
			testVar1 = var(@a, 123);
			testVar2 = var(@b, {100 : 100});
			function testVariant(var(a => int, b => dict(int, int)) testVar) {
				match (testVar) {
					:a(smth) {
						print(smth + 100);
					}
					:b(smth) {
						print(smth[100]);
					}
				}
			};
			testVariant(testVar2); // wypisze 100
			print('\n');
			testVariant(testVar1); // wypisze 223
			print('\n');

	-- is
		zwraca bool, przykład w pliku good/variants.vl
		
-- INSTRUKCJE DLA SŁOWNIKÓW
	Słownik ma zawsze określony typ dla kluczy oraz wartości, który jest definiowany w momencie deklaracji zmiennej słownikówej.
	Typem kluczów oraz wartości może byc dowaolny typ poza void-em.
	Nowa Instancja słownika tworzy się jak w Javascypt-ie (wartości do kluczy pobierają się też jak w JS).
	Przykład:
		dict(int, char) dTest;
		dTest = {
			1 : 'a',
			2 : 'b',
			3 : 'c'
		};
		print(dTest[2]); // wypisze b

-- INSTRUKCJE DLA LIST
	Dla list używamy instrukcji for

	Przykład instrukcji for:
		list(int) l;
		l = [1,2,3,4,5];
		for (int x in l) {
			print(x + 10);
		}; // wypisze 1112131415

-- WYPISYWANIE
	Varlang posiada wbudowany mechanizm do wypisywania na standardowe wyjście za pomocą wbudowanej instrukcji "print".
	Język nie ma typu string, ale w programie można wypisywać określony tekst za pomocą wywołania
		print("CosDoWypisania");
	Printowanie jest zaimplementowane dla wszystkich typów.
	Funkcja print nie wypisuje symbolu nowej linii, ale można to zrobić za pomocą wywołania
		print('\n');
	albo korzystając z zadeklarowanej wcześniej funkcji typu:
		function printLn(char x) {
			print(x);
			print('\n');
		}
	można również obsługiwać listę charów jako string za pomocą np. funkcji:
		function printStr(list(char) l) {
			for (char c in l) {
				print(c);
			};
			print('\n');
		};
-- TYPY

	Varlang ma następne wbudowane typy:
	- int
	- bool
	- list
	- dict
	- var
	- function
	- void - tylko dla procedur (definiują się jako funkkcję zwracające typ void)

	Każda zmienna w języku ma określony typ.

	Język posiada statyczne typowanie - czyli przed wykonaniem interpreter sprawdza całe ciało programu i w przypadku błędów wypisuje je na standardowe wyjśćie diagnostyczne.

	TypeChecker - moduł do sprawdzania typów sprawdz zgodność typów dla wszystkich elementów (dotyczy również funkcji, list, słowników -- przechodzi on całe drzewo programu)

-- FUNKCJE

	Język ma funkcję, które mogą zwracać albo nie zwracać (typ void) wynik.

	Funkcje przyjmują 

	Funkcje obsługują rekurencyjne wywołania.
	Przykład
		function rec(int x) {
			if (x > 1) {
				print('a');
				rec(x - 1);
			}
		};
		rec(10); // 9 razy wypisze symbol a

	Funkcje przyjmują argumenty (może ich być 0).
	TypeChecker sprawdza statycznie, czy każde wywołanie funkcji ma poprawne typowo argumenty (oraz ilośc zgodną z deklaracją)

	- Deklaracja zmiennych
	Przed wykorzystaniem zmiennej wcześniej należy podać jej typ oraz nazwę (identyfikator).
	Przykłady poprawne:
		int a;
		int b,c;
	Przykłady niepoprawne:
		int a, char x;

-- ZMIENNE
	Zmienne mogą być lokalne oraz globalne.
	Obsługa zmienncyh i pamięci jest zaimplementowana za pomocą dwóch słowników (Env(Ident -> Loc) oraz State(Loc -> Val)).
		Loc - to jest typ lokacji (u mnie Int).

-- PRZYKŁADY KODU
	Przykłady są w katalogach bad i good z komentarzami


-- OPIS IMPLEMENTACJI
	Rozwiązanie składa się z kilku części:
		- Kod wygenerowany przez bnfc
			parser kodu programu, przekształcający na abstrackcyjne typy opisane w pliku AbsVarlang.hs
		- Interpreter.hs
			moduł zawierający main, odczytujący zawartości plików programów
			uruchamia typechecker (statyczny)
			po przejściu (bezbłędnym) przez typechceker odpala interpreter (z modułu InterpreterUtils)
		- TypeChecker.hs
			moduł w pełni obsługujący statyczne sprawdzenie typów przed uruchomieniem programu.
			Korzysta z pomocniczego stanu (w postaci list map)
		- InterpreterUtils.hs
			moduł, obsługujący działanie programu (zakłada, że typy są wszędzie poprawne, co jest prawdą)
		- VarlangState.hs
			moduł opisujący typ stanu dla interpretera (dwie mapy + typ dla wartości) oraz standardowe operacji na obiekcie stanu
			interpretera
			

-- URUCHOMIENIE
	polecenie `make` - kompiluje interpreter do pliku interpreter
	./interpreter plik.hs -- odpala interpreter dla pliku
	./interpreter plik.hs plik2.hs  -- odpala interpreter dla plików
	./interpreter plik.hs plik2.hs -- DEBUG - odpala interpreter w trybie debugowania (wypisuję on wtedy dodatkową ininformację diagnostyczną)



