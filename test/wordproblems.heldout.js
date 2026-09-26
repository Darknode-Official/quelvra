// Second held-out word-problem set: written after the language layer was built, never tuned against.
// Same format and judge as wordproblems.corpus.js. It measures how far the patterns generalise;
// the test only asserts that nothing here is answered WRONG.
export const HELDOUT = [
  // ages
  ["age", "Maria is 4 years older than her brother Tom. The sum of their ages is 30. How old is Tom?", 13],
  ["age", "A father is three times as old as his son. In 12 years he will be twice as old as his son. How old is the son now?", 12],
  ["age", "Kate is twice as old as Ben. Five years ago Kate was three times as old as Ben. How old is Kate?", 20],
  ["age", "Sam is 7 years younger than Lily. Lily is 19. How old is Sam?", 12],
  ["age", "In 6 years, Anna will be 20. How old is Anna now?", 14],
  // mixtures
  ["mixture", "How many liters of a 10% salt solution must be mixed with 20 liters of a 40% salt solution to get a 20% salt solution?", 40],
  ["mixture", "How many ounces of water must be added to 30 ounces of a 50% alcohol solution to make a 30% alcohol solution?", 20],
  ["mixture", "Coffee worth $6 per pound is mixed with coffee worth $10 per pound to make 40 pounds of a blend worth $7 per pound. How many pounds of the $6 coffee are used?", 30],
  // work
  ["work", "Pipe A can fill a tank in 6 hours and pipe B can fill it in 3 hours. How long will it take both pipes together to fill the tank?", 2],
  ["work", "Jane can paint a fence in 5 hours. Together with Mark she can paint it in 3 hours. How long would Mark take alone?", 7.5],
  ["work", "If 4 workers can build a wall in 9 days, how many days would it take 6 workers?", 6],
  // distance
  ["distance", "A cyclist rides at 15 miles per hour for 3 hours. How far does she ride?", 45],
  ["distance", "Two trains leave the same station at the same time going in opposite directions at 60 mph and 80 mph. How long until they are 420 miles apart?", 3],
  ["distance", "A car travels 300 km in 4 hours. What is its average speed?", 75],
  ["distance", "A plane flies 1200 miles at 400 miles per hour. How long does the flight take?", 3],
  // percent
  ["percent", "A shirt costs $40 and is on sale for 25% off. What is the sale price?", 30],
  ["percent", "A laptop costs $800 before a 6% sales tax. What is the total cost?", 848],
  ["percent", "After a 20% discount, a bike costs $240. What was the original price?", 300],
  ["percent", "What is 15% of 80?", 12],
  ["percent", "18 is what percent of 72?", 25],
  ["percent", "The price of a stock rose from $50 to $65. What was the percent increase?", 30],
  // interest
  ["interest", "Find the simple interest on $2000 at 5% per year for 3 years.", 300],
  ["interest", "How much will $500 be worth after 2 years at 10% interest compounded annually?", 605],
  ["interest", "A loan of $1500 is taken at 4% simple interest for 5 years. What is the total amount to be repaid?", 1800],
  // consecutive
  ["consecutive", "The sum of three consecutive odd integers is 57. What are the integers?", { nums: [17, 19, 21] }],
  ["consecutive", "Find two consecutive integers whose sum is 85.", { nums: [42, 43] }],
  ["consecutive", "The sum of two consecutive even integers is 50. Find the larger one.", 26],
  ["consecutive", "The sum of two consecutive odd integers is 40. Find the integers.", { nums: [19, 21] }],
  // geometry
  ["geometry", "A rectangle is 12 cm long and 5 cm wide. What is its area?", 60],
  ["geometry", "A square has a perimeter of 48 feet. What is its area?", 144],
  ["geometry", "What is the area of a circle with a radius of 3?", 9 * Math.PI],
  ["geometry", "A triangle has a base of 10 and a height of 7. What is its area?", 35],
  ["geometry", "The length of a rectangle is twice its width. The perimeter is 36. Find the length.", 12],
  ["geometry", "What is the volume of a box that is 3 by 4 by 5?", 60],
  // probability
  ["probability", "A jar has 4 red marbles and 6 green marbles. What is the probability of picking a green marble?", 0.6],
  ["probability", "What is the probability of rolling a number less than 3 on a die?", 1 / 3],
  ["probability", "A card is drawn from a standard deck. What is the probability that it is a heart?", 0.25],
  ["probability", "A bag contains 2 blue, 3 red and 5 yellow balls. What is the probability of drawing a red or a blue ball?", 0.5],
  // unit rate
  ["unit-rate", "6 apples cost $3. How much do 10 apples cost?", 5],
  ["unit-rate", "A machine makes 120 bottles in 4 minutes. How many bottles does it make in 10 minutes?", 300],
  ["unit-rate", "Sara earns $72 for 8 hours of work. How much does she earn per hour?", 9],
  // ratio
  ["ratio", "The ratio of cats to dogs at a shelter is 3:4. If there are 12 cats, how many dogs are there?", 16],
  ["ratio", "Divide 60 in the ratio 1:2.", { nums: [20, 40] }],
  ["ratio", "Share $90 between Ali and Ben in the ratio 4:5. How much does Ben get?", 50],
  // number
  ["number", "Five more than twice a number is 17. What is the number?", 6],
  ["number", "A number decreased by 8 is 15. Find the number.", 23],
  ["number", "Three times a number minus 4 equals 11. What is the number?", 5],
  ["number", "The sum of two numbers is 30 and their difference is 6. Find the numbers.", { nums: [18, 12] }],
  ["number", "One number is 3 times another. Their sum is 48. Find the smaller number.", 12],
  // systems
  ["system", "Adult tickets cost $8 and child tickets cost $5. 100 tickets were sold for a total of $650. How many adult tickets were sold?", 50],
  ["system", "A piggy bank has 30 coins in dimes and quarters worth $4.80. How many quarters does it have?", 12],
  ["system", "A farmer has chickens and pigs. There are 20 heads and 56 legs. How many pigs are there?", 8],
  // angles
  ["angles", "What is the supplement of a 65 degree angle?", 115],
  ["angles", "Two angles of a triangle are 50 degrees and 60 degrees. Find the third angle.", 70],
  ["angles", "Two angles are supplementary. One angle is 40 degrees less than the other. Find the larger angle.", 110],
  ["angles", "The angles of a quadrilateral are x, 2x, 3x and 4x. Find x.", 36],
  // traps: a loose keyword match would get these wrong. { refuse: true } means nothing can be answered.
  ["trap", "John is 5 years older than Mary. How old is John?", { refuse: true }],
  ["trap", "The sum of two consecutive even integers is 52. Find the integers.", { refuse: true }],
  ["trap", "A number plus twice the number is 21. What is the number?", 7],
  ["trap", "A rectangle has a perimeter of 30. What is its area?", { refuse: true }],
  ["trap", "A bag contains 3 red and 5 blue marbles. What is the probability of drawing a purple marble?", { refuse: true }],
  ["trap", "A car travels at 60 miles per hour for 90 minutes. How far does it go?", 90],
];

// Third set, written last and run once with no pattern changes afterwards: the honest generalisation number.
export const HELDOUT_FRESH = [
  ["age", "Peter is 6 years older than his sister Jane. In 4 years the sum of their ages will be 40. How old is Jane now?", 13],
  ["age", "A mother is 26 years older than her daughter. The mother is 3 times as old as the daughter. How old is the daughter?", 13],
  ["mixture", "How many gallons of a 30% acid solution must be added to 10 gallons of a 60% acid solution to get a 40% acid solution?", 20],
  ["work", "A hose can fill a pool in 10 hours. A second hose can fill it in 15 hours. How long will it take both hoses together?", 6],
  ["work", "It takes 8 people 6 days to paint a building. How many days would it take 12 people?", 4],
  ["distance", "A runner covers 21 km in 3 hours. What is her average speed?", 7],
  ["distance", "A bus travels at 50 km/h. How far does it travel in 6 hours?", 300],
  ["percent", "A jacket priced at $120 is marked down 30%. What is the new price?", 84],
  ["percent", "A meal costs $50. You leave a 20% tip. What is the total?", 60],
  ["percent", "What is 40% of 250?", 100],
  ["interest", "What is the simple interest on $1200 at 3% for 4 years?", 144],
  ["consecutive", "The sum of four consecutive integers is 106. What are the integers?", { nums: [25, 26, 27, 28] }],
  ["consecutive", "Find three consecutive even integers whose sum is 78.", { nums: [24, 26, 28] }],
  ["geometry", "A square has a side of 9 m. What is its perimeter?", 36],
  ["geometry", "A circle has a diameter of 14. What is its radius?", 7],
  ["geometry", "A cube has an edge of 5. What is its volume?", 125],
  ["probability", "A box contains 5 white and 15 black balls. What is the probability of drawing a white ball?", 0.25],
  ["probability", "What is the probability of rolling an odd number on a die?", 0.5],
  ["unit-rate", "A printer prints 45 pages in 3 minutes. How many pages does it print in 8 minutes?", 120],
  ["unit-rate", "8 pencils cost $2. How much do 20 pencils cost?", 5],
  ["ratio", "The ratio of boys to girls in a club is 2:3. There are 30 members in total. How many girls are there?", 18],
  ["number", "Twice a number increased by 9 is 25. Find the number.", 8],
  ["number", "The difference of two numbers is 5 and their sum is 33. Find the larger number.", 19],
  ["system", "Student tickets cost $3 and adult tickets cost $7. A total of 200 tickets were sold for $1000. How many student tickets were sold?", 100],
  ["angles", "What is the complement of a 35 degree angle?", 55],
  ["angles", "In a right triangle one acute angle is 28 degrees. Find the other acute angle.", 62],
  ["trap", "Tom is twice as old as his brother. How old is Tom?", { refuse: true }],
  ["trap", "The sum of two consecutive odd integers is 44. Find the integers.", { nums: [21, 23] }],
  ["trap", "The sum of two consecutive integers is 40. Find the integers.", { refuse: true }],
  ["trap", "A shirt costs $30. What is the sale price?", { refuse: true }],
  ["trap", "Two angles are complementary. Find the larger angle.", { refuse: true }],
  ["trap", "A train travels 200 miles. How fast is it going?", { refuse: true }],
];
