// Everyday phrasings (plain student wording) that Quelvra must understand AND verify: each one is
// an answer, not a refusal (test/everyday.test.js). Expected values checked by hand.
const PI = Math.PI;
export const CASES = [
  ["arith", "whats 15 percent of 80", 12], ["arith", "what is 3/4 plus 2/3", 17 / 12], ["arith", "how much is 7 times 8", 56],
  ["arith", "percent change from 50 to 75", 50], ["arith", "what percent of 80 is 20", 25], ["arith", "20 is what percent of 80", 25],
  ["arith", "increase 80 by 15%", 92], ["arith", "decrease 80 by 15 percent", 68], ["arith", "convert 0.75 to a fraction", { re: /3\/4|3 \/ 4/ }],
  ["arith", "20% off 80", 64], ["arith", "sale price of 80 with 20% off", 64], ["arith", "$80 with 25% discount", 60],
  ["arith", "std dev of 2,4,6", { re: /sqrt\(6\).*3|standard deviation/ }],
  ["arith", "write 5/8 as a decimal", 0.625], ["arith", "3/8 as a percent", 37.5], ["arith", "simplify 18/24", { re: /3\/4|3 \/ 4/ }],
  ["arith", "what's the square root of 50", Math.sqrt(50)], ["arith", "simplify sqrt(50)", { re: /5.*sqrt\(2\)|5√2/ }], ["arith", "cube root of 64", 4],
  ["arith", "what is 2 to the power of 10", 1024], ["arith", "log base 2 of 8", 3], ["arith", "natural log of e squared", 2],
  ["arith", "round 3.14159 to 2 decimal places", 3.14], ["arith", "reciprocal of 4", 0.25], ["arith", "average of 4, 8 and 12", 8],
  ["arith", "lcm of 4 and 6", 12], ["arith", "greatest common factor of 24 and 36", 12], ["arith", "is 91 prime", { re: /91 is not prime: 91 = 7\*13/ }],
  ["arith", "prime factorization of 360", { re: /2\^3.*3\^2.*5/ }], ["arith", "what is 12 factorial", 479001600], ["arith", "10 choose 3", 120],
  ["arith", "absolute value of -7", 7], ["arith", "what is 17 mod 5", 2], ["arith", "remainder when 17 is divided by 5", 2],
  ["alg", "solve for x: 2x + 3 = 11", 4], ["alg", "find x if 3x - 7 = 8", 5], ["alg", "what is x when 5x = 35", 7], ["alg", "x/4 = 3, find x", 12],
  ["alg", "solve x^2 - 5x + 6 = 0", { roots: [2, 3] }], ["alg", "find the roots of x^2 - 9", { roots: [3, -3] }], ["alg", "factor x^2 + 5x + 6", { re: /\(x \+ 2\).*\(x \+ 3\)|\(x \+ 3\).*\(x \+ 2\)/ }],
  ["alg", "expand (x + 2)(x - 3)", { expr: "x^2 - x - 6" }], ["alg", "expand (x+1)^3", { expr: "x^3+3x^2+3x+1" }], ["alg", "simplify 2x + 3x - x", { expr: "4x" }],
  ["alg", "solve 2x + y = 7 and x - y = 2", { re: /x = 3.*y = 1/ }], ["alg", "solve the system x + y = 10, x - y = 2", { re: /x = 6.*y = 4/ }],
  ["alg", "solve 2x + 5 > 11", { re: /3 < x|x > 3/ }], ["alg", "solve |x - 3| = 5", { roots: [8, -2] }], ["alg", "complete the square x^2 + 6x + 5", { re: /\(x \+ 3\)\^2 - 4/ }],
  ["alg", "vertex of y = x^2 - 4x + 3", { re: /2.*-1/ }], ["alg", "discriminant of x^2 + 4x + 5", -4], ["alg", "evaluate 3x^2 + 2 when x = 4", 50],
  ["alg", "f(x) = 2x + 1, find f(3)", 7], ["alg", "if f(x) = x^2 - 1 what is f(5)", 24], ["alg", "inverse of f(x) = 2x + 3", { expr: "(x-3)/2" }],
  ["alg", "slope of the line through (1, 2) and (3, 8)", 3], ["alg", "equation of the line through (1, 2) and (3, 8)", { re: /y = 3x - 1|y = 3 x - 1/ }],
  ["alg", "distance between (0, 0) and (3, 4)", 5], ["alg", "midpoint of (2, 4) and (6, 8)", { re: /4.*6/ }], ["alg", "y intercept of y = 2x + 5", { re: /\(0, 5\)/ }],
  ["alg", "solve 2^x = 32", 5], ["alg", "solve log(x) = 2", 100], ["alg", "rationalize 1/sqrt(2)", { re: /sqrt\(2\) ?\/ ?2|√2/ }],
  ["alg", "domain of 1/(x - 2)", { re: /2/ }], ["alg", "what is the sum of the roots of x^2 - 7x + 10", 7],
  ["geo", "area of a circle with radius 5", 25 * PI], ["geo", "circumference of a circle with diameter 10", 10 * PI], ["geo", "area of a triangle with base 6 and height 4", 12],
  ["geo", "hypotenuse of a right triangle with legs 3 and 4", 5], ["geo", "area of a rectangle 5 by 8", 40], ["geo", "perimeter of a rectangle with length 5 and width 3", 16],
  ["geo", "volume of a sphere with radius 3", 36 * PI], ["geo", "volume of a cylinder radius 2 height 5", 20 * PI], ["geo", "surface area of a cube with side 3", 54],
  ["geo", "sum of interior angles of a hexagon", 720], ["geo", "each interior angle of a regular octagon", 135], ["geo", "area of a triangle with sides 3, 4 and 5", 6],
  ["geo", "diagonal of a square with side 5", 5 * Math.SQRT2], ["geo", "area of a trapezoid with bases 4 and 6 and height 3", 15], ["geo", "convert 180 degrees to radians", PI],
  ["geo", "sin of 30 degrees", 0.5], ["geo", "cos 60 degrees", 0.5], ["geo", "what is tan 45 degrees", 1],
  ["calc", "derivative of x^3", { expr: "3x^2" }], ["calc", "differentiate sin(x) * x", { expr: "cos(x)*x + sin(x)" }], ["calc", "what's the derivative of e^(2x)", { expr: "2e^(2x)" }],
  ["calc", "integrate x^2", { anti: "x^3/3" }], ["calc", "integral of 1/x", { anti: "ln(x)" }], ["calc", "integrate x^2 from 0 to 3", 9],
  ["calc", "area under y = x^2 from 0 to 2", 8 / 3], ["calc", "limit of sin(x)/x as x approaches 0", 1], ["calc", "limit as x goes to infinity of (2x+1)/(x-3)", 2],
  ["calc", "slope of the tangent to y = x^2 at x = 3", 6], ["calc", "find the maximum of -x^2 + 4x", 4], ["calc", "critical points of x^3 - 3x", { roots: [1, -1] }],
  ["calc", "second derivative of x^4", { expr: "12x^2" }], ["calc", "d/dx ln(x^2)", { expr: "2/x" }], ["calc", "taylor series of e^x", { re: /x\^2 ?\/ ?2|x\^2\/2/ }],
  ["seq", "sum of the first 100 positive integers", 5050], ["seq", "next number in 2, 4, 8, 16", 32], ["seq", "10th term of the arithmetic sequence 3, 7, 11", 39],
  ["seq", "sum of the geometric series 1 + 1/2 + 1/4 + ...", 2], ["seq", "what is the 10th fibonacci number", 55],
  ["stats", "mean of 5 10 15 20", 12.5], ["stats", "median of 7, 1, 3, 9", 5], ["stats", "what's the range of 4, 9, 2, 7", 7],
  ["prob", "probability of rolling an even number on a die", 0.5], ["prob", "odds of flipping heads twice", 0.25], ["prob", "how many ways can 5 people sit in a row", 120],
  ["word", "a shirt costs 40 dollars and is on sale for 25% off. what is the sale price?", 30],
  ["word", "if 3 pencils cost 75 cents, how much do 7 pencils cost?", 175],
  ["word", "a car travels 150 miles in 3 hours. what is its average speed?", 50],
  ["word", "sam is 3 times as old as his son. in 10 years he will be twice as old. how old is the son now?", 10],
  ["word", "the sum of two numbers is 20 and their difference is 4. what are the numbers?", { re: /12.*8|8.*12/ }],
  ["word", "a rectangle has a perimeter of 30 and its length is twice its width. find the width", 5],
  ["word", "i have 5 apples and eat 2. how many are left?", 3],
  ["word", "what is the tax on a 50 dollar item at 8 percent", 4],
  ["word", "how long does it take to travel 240 km at 60 km per hour", 4],
  ["word", "a recipe needs 2 cups of flour for 12 cookies. how much flour for 30 cookies?", 5],
  ["new", "raise 250 by 20 percent", 300], ["new", "cut 90 by 10%", 81], ["new", "what is 20% more than 50", 60], ["new", "15 percent less than 200", 170],
  ["new", "convert 3/4 to decimal", 0.75], ["new", "express 0.2 as a percentage", 20], ["new", "what is 7/20 as a percent", 35], ["new", "multiplicative inverse of 2/3", 1.5],
  ["new", "evaluate x^2 - 3x at x = 5", 10], ["new", "find the value of 2a + 7 when a = 3", 13], ["new", "let g(t) = t^2 + 1, find g(2)", 5], ["new", "given h(x) = 3x - 4 what is h(10)", 26],
  ["new", "3x + 1 = 10, solve for x", 3], ["new", "2y - 4 = 10. find y", 7], ["new", "median of 10 20 30", 20], ["new", "standard deviation of 2 4 4 4 5 5 7 9", Math.sqrt(32 / 7)],
  ["new", "the 12th fibonacci number", 144], ["new", "2 + 1 + 1/2 + ...", 4], ["new", "sum of the infinite series 5 + 1 + 1/5 + ...", 6.25],
  ["new", "chance of rolling a number greater than 4 on a die", 1 / 3], ["new", "probability of getting an odd number on a fair die", 0.5], ["new", "probability of flipping 3 heads in a row", 0.125],
  ["new", "total cost of a 40 dollar jacket with 5% tax", 42], ["new", "tax on 200 dollars at 7.5 percent", 15],
  ["new", "how long does it take to drive 300 miles at 60 miles per hour", 5], ["new", "how far does a car travel in 3 hours at 50 km per hour", 150],
  ["new", "if 4 notebooks cost 300 cents, how much do 6 notebooks cost?", 450], ["new", "volume of a cone radius 3 height 4", 12 * PI],
  ["new", "ella is 4 times as old as her daughter. in 20 years she will be twice as old. how old is the daughter now?", 10],
  ["new", "the log of 100 squared", 4], ["new", "square root of 3 squared", 3],
  ["v2-arith", "what's twelve times eleven", 132], ["v2-arith", "one hundred divided by eight", 12.5], ["v2-arith", "seventeen squared", 289],
  ["v2-arith", "the square of 13", 169], ["v2-arith", "cube of 4", 64], ["v2-arith", "what is 2 to the power of ten", 1024],
  ["v2-arith", "difference between 85 and 38", 47], ["v2-arith", "the product of 12 and 15", 180], ["v2-arith", "quotient of 144 and 12", 12],
  ["v2-arith", "sum of 1 through 100", 5050], ["v2-arith", "add all numbers from 1 to 50", 1275], ["v2-arith", "sum of the first 10 odd numbers", 100],
  ["v2-arith", "remainder when 100 is divided by 7", 2], ["v2-arith", "100 mod 7", 2], ["v2-arith", "what is half of 3/4", 0.375],
  ["v2-arith", "average of 4, 8 and 15", 9], ["v2-arith", "whats the mean of 3 7 8", 6], ["v2-arith", "range of 3 9 1 12", 11],
  ["v2-arith", "mode of 1 2 2 3 3 3", 3], ["v2-arith", "factorial of 6", 720], ["v2-arith", "6 factorial", 720],
  ["v2-arith", "gcd of 48 and 36", 12], ["v2-arith", "greatest common factor of 24 and 60", 12], ["v2-arith", "lowest common multiple of 4 and 6", 12],
  ["v2-arith", "round 3.14159 to 2 decimal places", 3.14], ["v2-arith", "round 1234 to the nearest hundred", 1200], ["v2-arith", "absolute value of -17", 17],
  ["v2-arith", "how many times does 7 go into 56", 8], ["v2-arith", "what number times 6 equals 42", 7], ["v2-arith", "what is 3 less than 20", 17],
  ["v2-arith", "square root of 144 plus 5", 17], ["v2-arith", "10 percent of 10 percent of 1000", 10], ["v2-money", "what percent of 80 is 20", 25],
  ["v2-money", "20 is what percent of 80", 25], ["v2-money", "30 is 15% of what number", 200], ["v2-money", "a shirt costs $40 and is 30% off, what is the sale price", 28],
  ["v2-money", "i paid 45 after a 10% discount, what was the original price", 50], ["v2-money", "simple interest on 1000 at 5% for 3 years", 150], ["v2-money", "compound interest on 1000 at 10% for 2 years", 210],
  ["v2-money", "how much is 1000 after 2 years at 10% compounded annually", 1210], ["v2-money", "if i save 25 dollars a week how much in a year", 1300], ["v2-money", "price went from 50 to 65, what is the percent increase", 30],
  ["v2-money", "percent decrease from 80 to 60", 25], ["v2-money", "what is 15 percent tip on 60", 9], ["v2-money", "split 120 dollars among 5 people", 24],
  ["v2-money", "3 apples cost 1.50, how much do 7 apples cost", 3.5], ["v2-money", "profit if bought for 80 and sold for 100", 20], ["v2-money", "profit percentage if cost price is 80 and selling price is 100", 25],
  ["v2-alg", "solve 5x - 3 = 17", 4], ["v2-alg", "if 3x = 21 what is x", 7], ["v2-alg", "x/4 = 5", 20],
  ["v2-alg", "find x if 2x + 3 = x + 10", 7], ["v2-alg", "a number plus 7 equals 19, what is the number", 12], ["v2-alg", "twice a number is 36, find the number", 18],
  ["v2-alg", "the sum of two consecutive numbers is 41, what is the smaller", 20], ["v2-alg", "slope of the line through (1,2) and (3,8)", 3], ["v2-alg", "distance between (0,0) and (3,4)", 5],
  ["v2-geo", "area of a circle with radius 3", 28.2743338823081], ["v2-geo", "circumference of a circle with diameter 10", 31.4159265358979], ["v2-geo", "area of a rectangle 5 by 8", 40],
  ["v2-geo", "perimeter of a square with side 7", 28], ["v2-geo", "area of a triangle with base 10 and height 6", 30], ["v2-geo", "hypotenuse of a right triangle with legs 5 and 12", 13],
  ["v2-geo", "volume of a cube with side 3", 27], ["v2-geo", "volume of a sphere radius 3", 113.097335529233], ["v2-geo", "area of a square with side 9", 81],
  ["v2-geo", "how many degrees in a triangle", 180], ["v2-geo", "sum of interior angles of a hexagon", 720], ["v2-geo", "each angle of a regular pentagon", 108],
  ["v2-geo", "diagonal of a square with side 1", 1.4142135623731], ["v2-geo", "surface area of a cube with side 2", 24], ["v2-geo", "area of a trapezoid with bases 4 and 6 and height 5", 25],
  ["v2-word", "a car travels 150 miles in 3 hours, what is its speed", 50], ["v2-word", "how long to drive 240 km at 80 km/h", 3], ["v2-word", "how far do you go in 2 hours at 60 mph", 120],
  ["v2-word", "if 5 workers take 8 days, how many days for 10 workers", 4], ["v2-word", "i have 3 boxes with 12 eggs each, how many eggs", 36], ["v2-word", "john has 5 apples and eats 2, how many are left", 3],
  ["v2-word", "sarah had 20 dollars and spent 7, how much does she have left", 13], ["v2-word", "there are 24 students and a third are boys, how many boys", 8], ["v2-word", "a pizza has 8 slices, 3 people eat 2 each, how many slices are left", 2],
  ["v2-word", "if a dozen eggs cost 3 dollars how much is one egg", 0.25], ["v2-word", "how many seconds in an hour", 3600], ["v2-word", "how many minutes in a day", 1440],
  ["v2-word", "how many hours in a week", 168], ["v2-word", "convert 5 km to miles", 3.10685596118667], ["v2-word", "how many inches in 3 feet", 36],
  ["v2-word", "what is 100 fahrenheit in celsius", 37.7777777777778], ["v2-word", "ratio 3:5, total 40, what is the larger part", 25], ["v2-calc", "what is the derivative of 3x^2 at x = 2", 12],
  ["v2-calc", "integral of 2x from 0 to 3", 9], ["v2-calc", "limit of (x^2-1)/(x-1) as x approaches 1", 2], ["v2-calc", "log base 2 of 64", 6],
  ["v2-calc", "log of 1000", 3], ["v2-calc", "e to the power 0", 1], ["v2-calc", "sin of 30 degrees", 0.5],
  ["v2-calc", "cos 60 degrees", 0.5], ["v2-calc", "tan of 45 degrees", 1],
  ["v2-alg", "solve x^2 = 49 for positive x", { re: /x = 7\b/ }], ["v2-word", "tom had 10 marbles and gave 3 to sam, how many does tom have", 7],
  // round 3: everyday verbs, percent word forms, number facts, sequences, series, limits
  ["v3-frac", "add 1/2 and 1/3", 0.833333333333333], ["v3-frac", "what is 2/3 of 3/4", 0.5], ["v3-frac", "1/2 divided by 1/4", 2],
  ["v3-frac", "subtract 1/4 from 3/4", 0.5], ["v3-frac", "0.125 as a fraction", 0.125], ["v3-frac", "what is 1.5 times 4", 6],
  ["v3-frac", "what is 3 and a half times 2", 7], ["v3-frac", "simplify 12/16", 0.75], ["v3-pct", "what is 25% of 25% of 400", 25],
  ["v3-pct", "40 is 20 percent of what", 200], ["v3-pct", "15 out of 20 as a percent", 75], ["v3-pct", "what percentage is 45 out of 60", 75],
  ["v3-pct", "i scored 18 out of 25, what percent is that", 72], ["v3-pct", "a population grows from 200 to 250, what is the percentage increase", 25], ["v3-pct", "a price of 80 is increased by 10% and then decreased by 10%", 79.2],
  ["v3-pct", "what is 150% of 60", 90], ["v3-pct", "0.5% of 2000", 10], ["v3-alg", "solve for x: 4(x - 2) = 12", 5],
  ["v3-alg", "3x + 2 = 2x + 9", 7], ["v3-alg", "if 2x - 7 = 11 find x", 9], ["v3-alg", "x + x + x = 27", 9],
  ["v3-alg", "what number added to 15 gives 42", 27], ["v3-alg", "a number divided by 4 is 9, what is the number", 36], ["v3-alg", "three times a number minus 5 is 16", 7],
  ["v3-alg", "the sum of three consecutive integers is 72, find the largest", 25], ["v3-alg", "solve 2x + y = 7 and x - y = 2 for x", 3], ["v3-alg", "if y = 3x + 2 and x = 4, what is y", 14],
  ["v3-exp", "what is 2 cubed times 3 squared", 72], ["v3-exp", "10 to the 6th", 1000000], ["v3-exp", "square root of 2 times square root of 8", 4],
  ["v3-exp", "4 to the half", 2], ["v3-exp", "what is 8 to the power of 1/3", 2], ["v3-exp", "5 squared minus 3 squared", 16],
  ["v3-exp", "how many zeros in a million", 6], ["v3-seq", "next number in the sequence 3 6 9 12", 15], ["v3-seq", "10th term of 2, 5, 8, 11", 29],
  ["v3-seq", "sum of the first 20 even numbers", 420], ["v3-seq", "what is the 5th term of a geometric sequence with first term 3 and ratio 2", 48], ["v3-geo", "area of a circle with diameter 10", 78.5398163397448],
  ["v3-geo", "radius of a circle with area 50", 3.98942280401433], ["v3-geo", "perimeter of a rectangle 7 by 3", 20], ["v3-geo", "area of an equilateral triangle with side 6", 15.5884572681199],
  ["v3-geo", "volume of a box 2 by 3 by 4", 24], ["v3-geo", "a square has area 64, what is its side", 8], ["v3-geo", "a circle has circumference 31.4, find its radius", 4.99746521308551],
  ["v3-geo", "third angle of a triangle with angles 50 and 60", 70], ["v3-geo", "complement of 35 degrees", 55], ["v3-geo", "supplement of 110 degrees", 70],
  ["v3-geo", "how many sides does a hexagon have", 6], ["v3-geo", "area of a semicircle with radius 4", 25.1327412287183], ["v3-stat", "average of 85, 90 and 95", 90],
  ["v3-stat", "what score do i need on the 4th test to average 80 if i got 70 75 and 85", 90], ["v3-stat", "mean of the first 10 natural numbers", 5.5], ["v3-stat", "median of 7, 1, 3, 9", 5],
  ["v3-stat", "range of the numbers 12 5 20 8", 15], ["v3-rate", "if i walk at 5 km/h how long to walk 12 km", 2.4], ["v3-rate", "a car uses 8 liters per 100 km, how many liters for 350 km", 28],
  ["v3-rate", "it takes 3 hours to paint 2 rooms, how long for 5 rooms", 7.5], ["v3-rate", "a tap fills 10 liters per minute, how long to fill 250 liters", 25], ["v3-rate", "how many minutes is 2.5 hours", 150],
  ["v3-rate", "how many hours is 150 minutes", 2.5], ["v3-rate", "earning 15 dollars an hour, how much for 40 hours", 600], ["v3-rate", "a recipe for 4 people needs 300 g of flour, how much for 6 people", 450],
  ["v3-num", "how many factors does 36 have", 9], ["v3-num", "smallest prime greater than 50", 53], ["v3-num", "sum of digits of 4567", 22],
  ["v3-num", "how many digits in 2^20", 7], ["v3-num", "10 factorial divided by 8 factorial", 90], ["v3-num", "roman numeral XIV", 14],
  ["v3a-calc", "derivative of ln(x) at x = 2", 0.5], ["v3a-calc", "integrate x^2 from 0 to 3", 9], ["v3a-calc", "integral of 1/x from 1 to e", 1],
  ["v3a-calc", "area under y = x^2 from 0 to 2", 2.66666666666667], ["v3a-calc", "limit of sin(x)/x as x goes to 0", 1], ["v3a-calc", "lim x->infinity of (1 + 1/x)^x", 2.71828182845905],
  ["v3a-calc", "find the maximum of -x^2 + 4x + 1", 5], ["v3a-calc", "minimum value of x^2 - 6x + 10", 1], ["v3a-calc", "slope of the tangent to y = x^3 at x = 2", 12],
  ["v3a-calc", "sum of 1/n^2 from 1 to infinity", 1.64493406684823], ["v3a-alg", "solve x^2 + 2x - 15 = 0", {"roots":[-5,3]}], ["v3a-alg", "roots of 2x^2 - 8", {"roots":[-2,2]}],
  ["v3a-alg", "solve |x - 3| = 5", {"roots":[-2,8]}], ["v3a-alg", "solve 2^x = 32", 5], ["v3a-alg", "solve log(x) = 2", 100],
  ["v3a-alg", "solve x^3 = 27", 3], ["v3a-alg", "discriminant of x^2 + 4x + 5", -4], ["v3a-trig", "sin 45 degrees", 0.707106781186548],
  ["v3a-trig", "cos(pi/3)", 0.5], ["v3a-trig", "arcsin(1/2) in degrees", 30], ["v3a-trig", "convert 180 degrees to radians", 3.14159265358979],
  ["v3a-trig", "convert pi/4 radians to degrees", 45], ["v3a-trig", "tan 60 degrees", 1.73205080756888], ["v3a-trig", "sec(0)", 1],
  ["v3a-log", "ln e^3", 3], ["v3a-log", "log base 3 of 81", 4], ["v3a-log", "log 2 + log 5", 1],
  ["v3a-log", "solve e^x = 10", 2.30258509299405], ["v3a-log", "how long to double money at 5% interest compounded annually", 14.2066990828905], ["v3a-cx", "modulus of 3 + 4i", 5],
  ["v3a-cx", "i^2", -1], ["v3a-la", "determinant of [[1,2],[3,4]]", -2], ["v3a-la", "dot product of (1,2,3) and (4,5,6)", 32],
  ["v3a-la", "magnitude of the vector (3, 4)", 5], ["v3a-comb", "how many ways can 5 people sit in a row", 120], ["v3a-comb", "8 choose 3", 56],
  ["v3a-comb", "number of permutations of 5 taken 2", 20], ["v3a-comb", "how many subsets does a set of 4 elements have", 16], ["v3a-comb", "how many arrangements of the letters in APPLE", 60],
  ["v3a-comb", "probability of rolling a sum of 7 with two dice", 0.166666666666667], ["v3a-comb", "probability of drawing an ace from a deck", 0.0769230769230769], ["v3a-comb", "expected value of a fair die", 3.5],
  ["v3a-comb", "how many handshakes among 10 people", 45], ["v3a-nt", "gcd(84, 126)", 42], ["v3a-nt", "17 mod 5", 2],
  ["v3a-nt", "3^100 mod 7", 4], ["v3a-nt", "last digit of 7^100", 1], ["v3a-nt", "number of divisors of 100", 9],
  ["v3a-nt", "sum of divisors of 12", 28], ["v3a-nt", "euler totient of 36", 12], ["v3a-nt", "binary 101101 to decimal", 45],
  ["v3a-st", "z score of 85 with mean 70 and standard deviation 10", 1.5], ["v3a-st", "probability that z is less than 1.96", 0.97500210485178], ["v3a-ser", "sum of the arithmetic series 2 + 5 + 8 + ... + 32", 187],
  ["v3a-ser", "sum of 1 + 2 + 4 + ... + 512", 1023], ["v3a-ser", "20th term of the arithmetic sequence 5, 9, 13", 81], ["v3a-ser", "sum from k = 1 to 10 of k^2", 385],
  ["v3-fix", "0b101101", 45], ["v3-fix", "0xff + 1", 256], ["v3-fix", "solve 2x + y = 7 and x - y = 2 for x", { re: /x = 3, y = 1/ }],
  ["v3-fix", "sum of 1/2^n from 0 to infinity", 2], ["v3-fix", "is 145 a perfect square", { re: /false/ }], ["v3-fix", "roman numeral MCMXCIV", 1994],
  // round 6: series, bases, primes, dice, vectors, mixed units, point-slope lines, word forms, precision
  ["r6-ser", "sum of 2^k for k from 0 to 10", 2047], ["r6-ser", "sum of the arithmetic series 3, 7, 11, ..., 99", 1275], ["r6-ser", "sum of 1, 2, 4, 8, ..., 1024", 2047],
  ["r6-ser", "1 + 1/2 + 1/4 + ... to infinity", 2], ["r6-ser", "1 + 1/3 + 1/9 + ... and so on", 1.5], ["r6-ser", "sum of 1/n^2 from n = 1 to infinity", PI * PI / 6],
  ["r6-nt", "is 2^31 - 1 prime", { re: /true|is prime/ }], ["r6-nt", "is 2^11 - 1 prime", { re: /false|not prime/ }], ["r6-nt", "0xff in decimal", 255],
  ["r6-nt", "convert 1010 base 2 to base 8", { re: /^12 \(base 8\)/ }], ["r6-nt", "0xff in binary", { re: /11111111/ }], ["r6-nt", "convert 777 base 8 to hex", { re: /1FF/ }],
  ["r6-nt", "zz base 36 to decimal", 1295], ["r6-prob", "probability of rolling a 6 twice in a row", 1 / 36], ["r6-prob", "chance of two sixes with two dice", 1 / 36],
  ["r6-prob", "probability of double six", 1 / 36], ["r6-prob", "odds of rolling a 6 three times in a row", 1 / 216],
  ["r6-geo", "angle between (1,0) and (0,1)", PI / 2], ["r6-geo", "angle between (1, 0) and (1, 1) in degrees", 45], ["r6-geo", "angle between (1, 2, 3) and (-2, 1, 0)", PI / 2],
  ["r6-geo", "equation of the line through (0,1) with slope 2", { re: /y = 2x \+ 1/ }], ["r6-geo", "line with slope 1/2 passing through (4, 1)", { re: /y = x\/2 - 1/ }],
  ["r6-geo", "line with slope 2 and y-intercept 3", { re: /y = 2x \+ 3/ }], ["r6-geo", "line through (2, 3) with gradient -1/2", { re: /y = -x\/2 \+ 4/ }],
  ["r6-unit", "3 hours 25 minutes in minutes", 205], ["r6-unit", "5 feet 10 inches in inches", 70], ["r6-unit", "how many seconds is 2 minutes 15 seconds", 135],
  ["r6-unit", "12 feet 3 inches in feet", 12.25], ["r6-unit", "2 pounds 4 ounces in ounces", 36], ["r6-unit", "1 hour 30 minutes in seconds", 5400], ["r6-unit", "1 km 200 m in m", 1200],
  ["r6-word", "a shirt costs 40 after a 20% discount, what was the original price", 50], ["r6-word", "if 3 apples cost 2.40, how much do 7 cost", 5.6],
  ["r6-word", "3 apples cost 2.40, how much do 7 cost", 5.6], ["r6-word", "two numbers add to 20 and differ by 4", { re: /x = 12, y = 8/ }],
  ["r6-word", "find two numbers whose sum is 20 and whose product is 96", { re: /x = 8, y = 12|x = 12, y = 8/ }], ["r6-word", "two integers sum to 30 and have a difference of 6", { re: /x = 18, y = 12/ }],
  ["r6-alg", "inequality 2x - 5 > 3", { re: /4 < x|x > 4/ }], ["r6-alg", "the inequality x^2 < 9", { re: /-3 < x < 3/ }], ["r6-alg", "inequality: 3x + 1 >= 7", { re: /2 <= x|x >= 2/ }],
  ["r6-prec", "sqrt(2) to 10 decimal places", { re: /1\.4142135624\b/ }], ["r6-prec", "pi to 50 digits", { re: /3\.1415926535897932384626433832795028841971693993751\b/ }],
  ["r6-prec", "22/7 to 8 decimal places", { re: /3\.14285714\b/ }], ["r6-prec", "1/3 to 5 significant figures", { re: /0\.33333\b/ }], ["r6-prec", "1/700 to 3 decimal places", { re: /0\.001\b/ }],
  ["r6-prec", "e to 30 decimal places", { re: /2\.718281828459045235360287471353\b/ }], ["r6-prec", "100*sqrt(2) to 2 decimal places", { re: /141\.42\b/ }],
  // round 7: quantities, counting, circle parts, finance, scale words, negative powers
  ["r7-qty", "how much is 3 dozen", 36], ["r7-qty", "half a dozen eggs", 6], ["r7-qty", "what is 1 million divided by 1 thousand", 1000], ["r7-qty", "1.5 million times 2", 3000000],
  ["r7-qty", "what is 10 to the negative 2", 0.01], ["r7-qty", "5 to the minus 1", 0.2],
  ["r7-count", "how many ways to choose a committee of 3 from 10 people", 120], ["r7-count", "how many ways can you pick 2 cards from 52", 1326], ["r7-count", "how many ways to arrange 3 of 8 books", 336],
  ["r7-count", "how many outcomes when flipping 4 coins", 16], ["r7-count", "how many outcomes when rolling 3 dice", 216], ["r7-count", "how many even numbers between 1 and 100", 50],
  ["r7-count", "how many odd numbers below 50", 25], ["r7-count", "how many multiples of 7 are there below 100", 14], ["r7-count", "how many multiples of 3 between 10 and 50", 13],
  ["r7-count", "how many primes are less than 50", 15], ["r7-count", "how many primes between 10 and 30", 6], ["r7-count", "how many primes up to 1000000", 78498], ["r7-count", "what is the 100th odd number", 199],
  ["r7-count", "what is the 7th even number", 14], ["r7-count", "primepi(100)", 25],
  ["r7-time", "what fraction of an hour is 45 minutes", 0.75],
  ["r7-time", "what percent of a day is 6 hours", 25], ["r7-time", "30 minutes is what fraction of a day", 1 / 48],
  ["r7-geo", "area of a parallelogram base 8 height 5", 40], ["r7-geo", "area of a rhombus with diagonals 6 and 8", 24], ["r7-geo", "perimeter of a semicircle with radius 7", 7 * PI + 14],
  ["r7-geo", "arc length of a 60 degree sector with radius 6", 2 * PI], ["r7-geo", "area of a sector with radius 6 and angle 60 degrees", 6 * PI],
  ["r7-geo", "area of a sector with radius 2 and angle pi/3 radians", 2 * PI / 3], ["r7-geo", "perimeter of a sector with radius 6 and central angle 90 degrees", 3 * PI + 12],
  ["r7-fin", "compound interest on 1000 at 5% for 3 years compounded monthly", { re: /161\.47\b/ }], ["r7-fin", "value of 1000 at 5% for 3 years compounded annually", 1157.625],
  ["r7-fin", "monthly payment on a 200000 loan at 6% for 30 years", { re: /1199\.1\b/ }], ["r7-fin", "future value of 500 a month at 6% for 10 years", { re: /81939\.67\b/ }],
  ["r7-fin", "how much do i need to invest at 4% to have 10000 in 5 years", { re: /8219\.27\b/ }],
];
// Phrasings that look everyday but have no single right answer from the words given: Quelvra must refuse them.
export const TRAPS = [
  "tom had 10 marbles and gave 3 to sam, how many does sam have", // the story tracks tom, not sam
  "how many days in a year", // 365 or 366; the units engine's Julian year would say 365.25
  "how many days in 3 years", // same: 1095 or 1096
  "there are 25 students and a third are boys, how many boys", // not a whole number of people
  "profit if bought for 100 and sold for 80", // that is a loss
  "each angle of a pentagon", // only a regular pentagon has one angle size
  "a pizza has 8 slices, 5 people eat 2 each, how many slices are left", // more than there is
  "if 5 workers take 8 days, how many hours for 10 workers", // units disagree
  "3 apples cost 1.50, how much do 7 pears cost", // a different item
  "add x and 3", // "add" is a verb, not a*d*d
  "mean of the first 0 natural numbers", // there are none
  "what is the 0th term of a geometric sequence with first term 3 and ratio 2", // terms start at 1
  "2 to the half of 8", // "to the half" is a power only when nothing follows
  "i scored 30 out of 25, what percent is that", // more than the total
  "a population grows from 250 to 200, what is the percentage increase", // that is a decrease
  "third angle of a triangle with angles 100 and 90", // no such triangle
  "complement of 95 degrees", // only angles below 90 have one
  "permutations of 3 taken 5", // cannot take more than there are
  "roman numeral IIII", // not a valid numeral
  "probability of rolling three 6s with two dice", // two dice cannot show three faces
  "3 apples 2 pears in fruit", // not units of one dimension
  "3 minutes 25 hours in minutes", // the bigger unit comes first
  "convert 1012 base 2 to base 8", // 2 is not a binary digit
  "sum of the arithmetic series 3, 7, 11, ..., 100", // 100 is not a term of the series
  "angle between (0,0) and (1,1)", // the zero vector has no direction
  "angle between (1,2) and (1,2,3)", // dimensions differ
  "x^2 + 1 to 5 decimal places", // not a constant
  "how many ways to choose a committee of 12 from 10 people", // cannot choose more than there are
  "how many outcomes when flipping 100 coins", // beyond the supported size (2^100 is fine, but the pattern caps at 60)
  "area of a sector with radius 6 and angle 400 degrees", // more than a full turn
  "what fraction of a minute is 3 hours", // the smaller unit must be asked about
  "what fraction of an hour is 45 apples", // not a unit of time
];
