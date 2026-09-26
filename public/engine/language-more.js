// More English patterns for the language engine: probability, statistics, counting, complex
// numbers, sequences and series, geometry formulas, number theory, polynomials, logs and
// everyday word problems. Like language.js these only TRANSLATE: every pattern produces math
// text (a formula or a command call) and shows the model it used in `interpretation`; the engine
// computes and verifies the value. A pattern returns null when its reading is not certain.

const N = String.raw`-?\d+(?:\.\d+)?(?:/\d+)?`;
const NUMS = String.raw`\[?\s*(${N}(?:\s*(?:,|;|\band\b|\s)\s*${N})+)\s*\]?`;
const nums = (s) => s.replace(/[[\]]/g, "").split(/\s*(?:,|;|\band\b|\s)\s*/).filter(Boolean);
const csv = (s) => nums(s).join(", ");
const num = String.raw`(${N})`;
const WORD_NUM = { one: 1, two: 2, three: 3, four: 4, five: 5, six: 6, seven: 7, eight: 8, nine: 9, ten: 10, eleven: 11, twelve: 12 };
const nOf = (s) => (WORD_NUM[String(s).toLowerCase()] !== undefined ? String(WORD_NUM[String(s).toLowerCase()]) : s);
const POLYGONS = { triangle: 3, quadrilateral: 4, square: 4, pentagon: 5, hexagon: 6, heptagon: 7, octagon: 8, nonagon: 9, decagon: 10, hendecagon: 11, dodecagon: 12, icosagon: 20 };
const sidesOf = (s) => {
  let m;
  if ((m = /^(\d+)[- ]?(?:gon|sided polygon)$/i.exec(s))) return m[1];
  if ((m = /^polygon with (\d+) sides$/i.exec(s))) return m[1];
  return POLYGONS[String(s).toLowerCase()] ? String(POLYGONS[String(s).toLowerCase()]) : null;
};
const BASES = { binary: 2, bin: 2, octal: 8, oct: 8, decimal: 10, hexadecimal: 16, hex: 16, ternary: 3 };
const baseOf = (s) => { const m = /^base[- ]?(\d+)$/i.exec(s); return m ? Number(m[1]) : BASES[String(s).toLowerCase()] || null; };
// cards: how many of the 52 have the property (rank 4, suit 13, colour 26, face card 12)
const CARD = { ace: ["rank", 4], king: ["rank", 4], queen: ["rank", 4], jack: ["rank", 4], heart: ["suit", 13], spade: ["suit", 13], club: ["suit", 13], diamond: ["suit", 13],
  "red card": ["colour", 26], "black card": ["colour", 26], "face card": ["face", 12] };
const cardOf = (s) => { const k = String(s).toLowerCase().replace(/s$/, "").replace(/^(?:a|an|the) /, ""); return CARD[k] ? [k, ...CARD[k]] : null; };
// overlap of two card properties (rank x suit = 1, same kind = 0 for different values)
function cardOverlap(a, b) {
  const kinds = [a[1], b[1]].sort().join("+");
  if (a[0] === b[0]) return a[2];
  if (kinds === "rank+suit") return 1;
  if (kinds === "colour+suit") return (/red/.test(a[0] + b[0]) && /heart|diamond/.test(a[0] + b[0])) || (/black/.test(a[0] + b[0]) && /spade|club/.test(a[0] + b[0])) ? 13 : 0;
  if (kinds === "colour+rank") return 2;
  if (kinds === "face+rank") return /king|queen|jack/.test(a[0] + b[0]) ? 4 : 0;
  if (kinds === "face+suit") return 3;
  if (kinds === "colour+face") return 6;
  return null; // two different ranks or two different suits: disjoint, but say so via 0 below
}
function letterCounts(word) {
  const c = new Map();
  for (const ch of word.toUpperCase()) c.set(ch, (c.get(ch) || 0) + 1);
  return [...c.entries()];
}
// "0.333..." / "0.1666..." / "0.142857142857...": the repeating block at the end
function repeatingDecimal(s) {
  const m = /^(\d*)\.(\d+)(?:\.\.\.|…)$/.exec(s);
  if (!m) return null;
  const [, ip, digits] = m;
  for (let len = 1; len <= Math.floor(digits.length / 2); len++) {
    const block = digits.slice(-len);
    let reps = 0, end = digits.length;
    while (end - len >= 0 && digits.slice(end - len, end) === block) { reps++; end -= len; }
    if (reps >= 2 && (len > 1 || reps >= 3 || digits.length === 2)) {
      const pre = digits.slice(0, end);
      return { ip: ip || "0", pre, block };
    }
  }
  return null;
}

export function morePatterns({ expr, mathOf, LEAD, re }) {
  const E = (s) => mathOf(s) || null;
  const out = (math, interpretation, extra = {}) => (math ? { math, interpretation, ...extra } : null);
  return [
    // ---------------------------------------------------------------- probability
    { id: "prob-die", re: /^(?:what is )?(?:the )?probability (?:of )?(?:rolling|getting|throwing) (?:a|an) (\d) (?:on|with) (?:a |one )?(?:fair |single |standard |six[- ]sided )*(?:die|dice)$/i,
      build: (m) => (+m[1] >= 1 && +m[1] <= 6 ? out("1/6", `one favourable face out of 6 equally likely faces: 1/6`) : null) },
    { id: "prob-dice-sum", re: /^(?:what is )?(?:the )?probability (?:of )?(?:rolling|getting|throwing) (?:a (?:sum|total) of )?(\d+)(?: as the (?:sum|total))? (?:with|on|using) (?:two|2|a pair of) (?:fair )?dice$/i,
      build: (m) => { const s = +m[1]; return s >= 2 && s <= 12 ? out(`(6 - abs(${s} - 7))/36`, `two dice: 36 equally likely outcomes, of which 6 - |${s} - 7| give a sum of ${s}`) : null; } },
    { id: "prob-dice-sum", re: /^(?:what is )?(?:the )?probability (?:of )?(?:getting |rolling )?(?:a (?:sum|total) of )?(\d+) (?:when|by|if) (?:rolling|throwing|you roll) (?:two|2|a pair of) (?:fair )?dice$/i,
      build: (m) => { const s = +m[1]; return s >= 2 && s <= 12 ? out(`(6 - abs(${s} - 7))/36`, `two dice: 36 equally likely outcomes, of which 6 - |${s} - 7| give a sum of ${s}`) : null; } },
    { id: "prob-dice-doubles", re: /^(?:what is )?(?:the )?probability (?:of )?(?:rolling|getting|throwing) (?:a )?doubles? (?:with|on|using) (?:two|2|a pair of) (?:fair )?dice$/i,
      build: () => out("6/36", "two dice: 6 doubles out of 36 equally likely outcomes") },
    { id: "prob-coins", re: /^(?:what is )?(?:the )?probability (?:of )?(?:getting |flipping |tossing )?(exactly|at least|at most|more than|fewer than|less than) (\w+) (heads?|tails?) (?:in|when flipping|when tossing|with|from) (\w+) (?:fair )?(?:coin )?(?:flips|tosses|throws|coins|times)$/i,
      build: (m) => {
        const k = nOf(m[2]), n = nOf(m[4]);
        if (!/^\d+$/.test(k) || !/^\d+$/.test(n) || +k > +n) return null;
        const q = m[1].toLowerCase();
        const math = q === "exactly" ? `binompdf(${n}, 1/2, ${k})` : q === "at most" ? `binomcdf(${n}, 1/2, ${k})` : q === "at least" ? `1 - binomcdf(${n}, 1/2, ${+k - 1})`
          : q === "more than" ? `1 - binomcdf(${n}, 1/2, ${k})` : `binomcdf(${n}, 1/2, ${+k - 1})`;
        return out(math, `number of ${m[3].replace(/s$/, "")}s in ${n} fair flips is Binomial(n = ${n}, p = 1/2); P(${q} ${k})`);
      } },
    { id: "prob-coins", re: /^(?:what is )?(?:the )?probability (?:of )?(?:getting )?(?:at least one|one or more) (head|tail)s? (?:in|when flipping|when tossing|with) (\w+) (?:fair )?(?:coin )?(?:flips|tosses|coins|throws)$/i,
      build: (m) => { const n = nOf(m[2]); return /^\d+$/.test(n) ? out(`1 - (1/2)^${n}`, `complement of no ${m[1]}s in ${n} fair flips: 1 - (1/2)^${n}`) : null; } },
    { id: "prob-coins", re: /^(?:what is )?(?:the )?probability (?:of )?(?:getting )?all (heads|tails) (?:in|when flipping|with) (\w+) (?:fair )?(?:coin )?(?:flips|tosses|coins)$/i,
      build: (m) => { const n = nOf(m[2]); return /^\d+$/.test(n) ? out(`(1/2)^${n}`, `each of ${n} independent fair flips shows ${m[1]}: (1/2)^${n}`) : null; } },
    { id: "prob-card", re: /^(?:what is )?(?:the )?probability (?:of )?(?:drawing|picking|getting|choosing|selecting) (?:a|an) ([a-z ]+?) (?:from|out of) (?:a |the )?(?:standard |well[- ]shuffled |shuffled )*(?:deck(?: of (?:52 )?(?:playing )?cards)?|52[- ]card deck)$/i,
      build: (m) => { const c = cardOf(m[1]); return c ? out(`${c[2]}/52`, `${c[2]} of the 52 equally likely cards are ${c[0]}s`) : null; } },
    { id: "prob-card", re: /^(?:what is )?(?:the )?probability (?:that )?a (?:card|randomly drawn card|card drawn at random)(?: from a (?:standard )?deck)? is (?:a|an) ([a-z ]+?) or (?:a|an) ([a-z ]+?)$/i,
      build: (m) => {
        const a = cardOf(m[1]), b = cardOf(m[2]);
        if (!a || !b) return null;
        let both = cardOverlap(a, b);
        if (both === null) both = 0;
        return out(`(${a[2]} + ${b[2]} - ${both})/52`, `inclusion-exclusion: P(${a[0]} or ${b[0]}) = (${a[2]} + ${b[2]} - ${both} in both)/52`);
      } },
    { id: "prob-card", re: /^(?:what is )?(?:the )?probability (?:of )?(?:drawing|picking|getting|choosing|selecting) (?:a|an) ([a-z ]+?) or (?:a|an) ([a-z ]+?)(?: (?:from|out of) (?:a |the )?(?:standard |shuffled )*(?:deck(?: of (?:52 )?(?:playing )?cards)?|52[- ]card deck))?$/i,
      build: (m) => {
        const a = cardOf(m[1]), b = cardOf(m[2]);
        if (!a || !b) return null;
        const both = cardOverlap(a, b) ?? 0; // null: two different ranks / suits / colours, disjoint
        return out(`(${a[2]} + ${b[2]} - ${both})/52`, `inclusion-exclusion: P(${a[0]} or ${b[0]}) = (${a[2]} + ${b[2]} - ${both} in both)/52`);
      } },
    { id: "prob-card", re: /^(?:what is )?(?:the )?probability (?:of )?(?:drawing|picking|getting|dealing) (\w+) (aces|kings|queens|jacks|hearts|spades|clubs|diamonds|red cards|black cards|face cards) (?:in a row )?(?:from a (?:standard )?deck(?: of cards)?)?,? ?(without|with) replacement$/i,
      build: (m) => {
        const k = nOf(m[1]), c = cardOf(m[2]);
        if (!/^\d+$/.test(k) || !c || +k > c[2]) return null;
        return /without/i.test(m[3])
          ? out(`hypergeompdf(52, ${c[2]}, ${k}, ${k})`, `${k} cards drawn without replacement, all ${c[0]}s: C(${c[2]}, ${k}) / C(52, ${k})`)
          : out(`(${c[2]}/52)^${k}`, `${k} independent draws with replacement, each a ${c[0]}: (${c[2]}/52)^${k}`);
      } },
    { id: "prob-binomial", re: /^(?:the )?binomial (?:probability|pmf|distribution)(?: with| for)?:? n ?= ?(\d+),? p ?= ?([\d./]+),? (?:and )?(k|x) ?= ?(\d+)$/i,
      build: (m) => out(`binompdf(${m[1]}, ${m[2]}, ${m[4]})`, `P(X = ${m[4]}) for X ~ Binomial(n = ${m[1]}, p = ${m[2]})`) },
    { id: "prob-geometric", re: /^(?:the )?(?:geometric )?probability (?:that the |of the |of )?first success (?:is |occurs )?on (?:the )?trial (\d+) (?:with|if|when) p ?= ?([\d./]+)$/i,
      build: (m) => out(`geompdf(${m[2]}, ${m[1]})`, `geometric distribution: ${+m[1] - 1} failures then a success, (1 - p)^${+m[1] - 1} p with p = ${m[2]}`) },
    { id: "prob-expected-die", re: /^(?:what is )?(?:the )?(?:expected value|expectation|mean) (?:of )?(?:(?:the )?(?:roll|outcome) of )?(?:a |one )?(?:fair )?(?:(\d+)[- ]sided )?(?:die|dice)(?: roll)?$/i,
      build: (m) => { const n = m[1] || "6"; return out(`(${n} + 1)/2`, `a fair ${n}-sided die: E = (1 + 2 + ... + ${n})/${n} = (${n} + 1)/2`); } },
    { id: "prob-independent", re: /^(?:find |what is )?p\((\w) (and|or|∩|∪) (\w)\) (?:if|when|given|with) p\(\1\) ?= ?([\d./]+),? (?:and )?p\(\3\) ?= ?([\d./]+),? (?:and )?(?:the events are |they are |a and b are )?(independent|mutually exclusive|disjoint)$/i,
      build: (m) => {
        const and = /and|∩/.test(m[2]), ind = /independent/i.test(m[6]);
        const math = and ? (ind ? `${m[4]} * ${m[5]}` : "0") : ind ? `${m[4]} + ${m[5]} - ${m[4]} * ${m[5]}` : `${m[4]} + ${m[5]}`;
        const why = and ? (ind ? "independent events: P(A and B) = P(A) P(B)" : "mutually exclusive events cannot both happen") : ind ? "P(A or B) = P(A) + P(B) - P(A) P(B) for independent events" : "mutually exclusive: P(A or B) = P(A) + P(B)";
        return out(math, why);
      } },
    { id: "prob-conditional", re: /^(?:find |what is )?p\((\w) ?\| ?(\w)\)(?: = p\(\1 and \2\) ?\/ ?p\(\2\))? (?:if|when|given|with) p\(\1 (?:and|∩) \2\) ?= ?([\d./]+),? (?:and )?p\(\2\) ?= ?([\d./]+)$/i,
      build: (m) => out(`(${m[3]}) / (${m[4]})`, `conditional probability: P(${m[1]} | ${m[2]}) = P(${m[1]} and ${m[2]}) / P(${m[2]})`) },

    // ---------------------------------------------------------------- statistics
    { id: "stats-pop", re: re(`^${LEAD}population (standard deviation|variance|sd|std) (?:of )?(?:the (?:data|numbers|values) )?${NUMS}$`),
      build: (m) => out(`${/var/i.test(m[1]) ? "pvariance" : "pstdev"}(${csv(m[2])})`, `population ${/var/i.test(m[1]) ? "variance" : "standard deviation"} (divide by n) of ${csv(m[2])}`) },
    { id: "stats-sample", re: re(`^${LEAD}sample (standard deviation|variance|sd|std) (?:of )?(?:the (?:data|numbers|values) )?${NUMS}$`),
      build: (m) => out(`${/var/i.test(m[1]) ? "variance" : "stdev"}(${csv(m[2])})`, `sample ${/var/i.test(m[1]) ? "variance" : "standard deviation"} (divide by n - 1) of ${csv(m[2])}`) },
    { id: "stats-range", re: re(`^${LEAD}range (?:of )?(?:the )?(?:data|data set|numbers|values|set)?:? ?${NUMS}$`),
      build: (m) => out(`datarange(${csv(m[1])})`, `range = largest - smallest of ${csv(m[1])}`) },
    { id: "stats-quartile", re: re(`^${LEAD}(first|lower|third|upper|1st|3rd)? ?quartiles? (?:of )?(?:the (?:data|numbers|values) )?${NUMS}$`),
      build: (m) => out(`quartiles(${csv(m[2])})`, `quartiles of ${csv(m[2])}${m[1] ? ` (the ${/first|lower|1st/i.test(m[1]) ? "first quartile is Q1" : "third quartile is Q3"})` : ""}`) },
    { id: "stats-iqr", re: re(`^${LEAD}(?:interquartile range|iqr) (?:of )?(?:the (?:data|numbers|values) )?${NUMS}$`),
      build: (m) => out(`iqr(${csv(m[1])})`, `interquartile range Q3 - Q1 of ${csv(m[1])}`) },
    { id: "stats-z", re: re(`^${LEAD}z[- ]?score (?:of|for) ${num} (?:with|if|when|given)(?: a)? mean (?:of |is |= ?)?${num},? (?:and )?(?:a )?(?:standard deviation|sd|sigma) (?:of |is |= ?)?${num}$`),
      build: (m) => out(`zscore(${m[1]}, ${m[2]}, ${m[3]})`, `z = (x - mean) / sd = (${m[1]} - ${m[2]}) / ${m[3]}`) },
    { id: "stats-sum", re: re(`^${LEAD}(sum|total|product) (?:of )?(?:the (?:numbers|values|data) )?${NUMS}$`),
      build: (m) => { const xs = nums(m[2]); return out(xs.map((x) => (x.startsWith("-") ? `(${x})` : x)).join(/prod/i.test(m[1]) ? " * " : " + "), `${m[1].toLowerCase()} of ${xs.join(", ")}`); } },
    { id: "stats-wmean", re: re(`^${LEAD}weighted (?:mean|average) (?:of )?${NUMS} (?:with|using) weights ${NUMS}$`),
      build: (m) => out(`wmean([${csv(m[1])}], [${csv(m[2])}])`, `weighted mean: sum(w x) / sum(w) with x = ${csv(m[1])} and w = ${csv(m[2])}`) },
    { id: "stats-corr", re: re(`^${LEAD}(?:pearson )?correlation(?: coefficient)? (?:of|between|for) (?:x ?= ?)?\\[([^\\]]+)\\] and (?:y ?= ?)?\\[([^\\]]+)\\]$`),
      build: (m) => out(`corr([${csv(m[1])}], [${csv(m[2])}])`, `Pearson correlation coefficient r of x = [${csv(m[1])}] and y = [${csv(m[2])}]`) },
    { id: "stats-regression", re: re(`^${LEAD}(?:least[- ]squares |linear )?regression(?: line| equation)? (?:of|for|through) (?:x ?= ?)?\\[([^\\]]+)\\] and (?:y ?= ?)?\\[([^\\]]+)\\]$`),
      build: (m) => out(`linreg([${csv(m[1])}], [${csv(m[2])}])`, `least-squares line y = m x + b for x = [${csv(m[1])}], y = [${csv(m[2])}]`) },
    { id: "stats-invnorm", re: re(`^${LEAD}(?:z[- ]?(?:score|value) (?:for|with|that has|such that)|inverse normal (?:of|for)) (?:an? )?(?:area|probability|percentile)?(?: to the left| below| less than)?(?: of| =)? ?(${N})$`),
      build: (m) => out(`invnorm(${m[1]})`, `the z with P(Z < z) = ${m[1]} for the standard normal`) },

    // ---------------------------------------------------------------- counting
    { id: "count-letters", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?(?:distinct |different |unique )?(?:ways (?:are there )?to arrange|arrangements of|permutations of|anagrams of|ways (?:can|to) (?:you )?(?:re)?arrange) (?:all )?(?:the )?(?:letters (?:of|in) )?(?:the word )?"?([A-Za-z]{2,20})"?(?: be arranged)?$/i,
      build: (m) => {
        if (/^(?:the|all|letters|objects|things|people|items)$/i.test(m[1])) return null;
        const c = letterCounts(m[1]);
        const repeated = c.filter(([, k]) => k > 1);
        return out(`multinomial(${c.map(([, k]) => k).join(", ")})`, `${m[1].length} letters${repeated.length ? `, with ${repeated.map(([l, k]) => `${l} x${k}`).join(", ")} repeated` : ", all different"}: ${m[1].length}! / (product of the repeat counts factorial)`);
      } },
    { id: "count-perm", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?(?:permutations|arrangements|orderings|ways to (?:arrange|order|line up)) (?:of )?(\w+) (?:distinct |different )?(?:objects|items|things|people|books|letters|students|elements|cards)?(?: in a (?:row|line))?(?: taken (\w+) at a time)?$/i,
      build: (m) => {
        const n = nOf(m[1]), k = m[2] && nOf(m[2]);
        if (!/^\d+$/.test(n) || (k && !/^\d+$/.test(k))) return null;
        return k ? out(`nPr(${n}, ${k})`, `ordered choices of ${k} from ${n}: ${n}!/(${n} - ${k})!`) : out(`${n}!`, `all orderings of ${n} distinct objects: ${n}!`);
      } },
    { id: "count-perm", re: /^(?:in )?how many (?:different )?ways can (\w+) (?:distinct |different )?(?:people|objects|items|things|books|letters|students|children|cars|runners|guests) (?:be |stand |sit )?(?:arranged|ordered|lined up|seated|placed|stand|sit)(?: in a (?:row|line))?$/i,
      build: (m) => { const n = nOf(m[1]); return /^\d+$/.test(n) ? out(`${n}!`, `all orderings of ${n} distinct objects: ${n}!`) : null; } },
    { id: "word-a-number", re: /^(?:the )?(sum|difference|product|quotient) of a number and (-?\d+(?:\.\d+)?) is (-?\d+(?:\.\d+)?)$/i,
      build: (m) => { const op = { sum: "+", difference: "-", product: "*", quotient: "/" }[m[1].toLowerCase()]; return out(`x ${op} ${m[2]} = ${m[3]}`, `let the number be x: x ${op} ${m[2]} = ${m[3]}`, { goal: "solve", variable: "x" }); } },
    { id: "count-choose", re: /^(?:find )?(?:the )?(?:number of ways|how many ways|in how many ways)(?: are there| can (?:you|we|one|i))? (?:to )?(?:choose|select|pick|form a (?:committee|team|group) of) (\w+) (?:\w+ )?(?:from|out of|among) (?:a (?:group|class|set) of )?(\w+)(?: \w+)?$/i,
      build: (m) => { const k = nOf(m[1]), n = nOf(m[2]); return /^\d+$/.test(k) && /^\d+$/.test(n) ? out(`binomial(${n}, ${k})`, `unordered choice of ${k} from ${n}: C(${n}, ${k})`) : null; } },
    { id: "count-arrange-k", re: /^(?:find )?(?:the )?(?:number of ways|how many ways)(?: are there| can (?:you|we|one))? (?:to )?(?:arrange|order|line up|seat) (\w+) (?:\w+ )?(?:from|out of|of) (\w+)(?: \w+)?$/i,
      build: (m) => { const k = nOf(m[1]), n = nOf(m[2]); return /^\d+$/.test(k) && /^\d+$/.test(n) ? out(`nPr(${n}, ${k})`, `ordered arrangement of ${k} from ${n}: ${n}!/(${n} - ${k})!`) : null; } },
    { id: "count-stars-bars", re: /^(?:find |what is )?(?:the )?(?:number of ways|how many ways)(?: are there| can (?:you|we|one))? (?:to )?(?:put|distribute|place|divide|share) (\w+) (?:identical|indistinguishable|identical|same) (?:\w+ )?(?:into|among|between|to) (\w+) (?:distinct |different |distinguishable )?(?:boxes|bins|children|kids|people|groups|urns|jars)(?: \(?(?:empty (?:boxes )?allowed|boxes can be empty)\)?)?$/i,
      build: (m) => { const n = nOf(m[1]), k = nOf(m[2]); return /^\d+$/.test(n) && /^\d+$/.test(k) ? out(`binomial(${n} + ${k} - 1, ${k} - 1)`, `stars and bars (empty allowed): C(${n} + ${k} - 1, ${k} - 1)`) : null; } },
    { id: "count-subsets", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?subsets (?:(?:does )?(?:of )?a set (?:with|of|having) (\w+) elements(?: have)?)$/i,
      build: (m) => { const n = nOf(m[1]); return /^\d+$/.test(n) ? out(`2^${n}`, `each of ${n} elements is in or out: 2^${n}`) : null; } },
    { id: "count-diagonals", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?diagonals (?:of|in|does) (?:a |an )?(?:regular )?([\w -]+?)(?: have)?$/i,
      build: (m) => { const n = sidesOf(m[1]); return n ? out(`${n}*(${n} - 3)/2`, `${n} vertices, each joined to ${n} - 3 non-neighbours, each diagonal counted twice: n(n - 3)/2`) : null; } },
    { id: "count-pins", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?(?:possible )?(\w+)[- ]digit (?:pins?|pin codes?|codes?|passcodes?|combinations?)(?: are (?:there|possible))?$/i,
      build: (m) => { const k = nOf(m[1]); return /^\d+$/.test(k) ? out(`10^${k}`, `${k} positions, 10 digits each (repeats and leading zeros allowed): 10^${k}`) : null; } },
    { id: "count-pins", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?(\w+)[- ]digit (?:positive )?(?:numbers|integers|whole numbers)(?: are (?:there|possible))?$/i,
      build: (m) => { const k = nOf(m[1]); return /^\d+$/.test(k) && +k >= 1 ? out(`9 * 10^(${k} - 1)`, `first digit 1-9, the other ${+k - 1} any of 10: 9 x 10^(${k} - 1)`) : null; } },
    { id: "count-derange", re: /^(?:find |what is |how many )?(?:the )?(?:number of )?derangements (?:of )?(\w+)(?: (?:objects|items|letters|elements))?$/i,
      build: (m) => { const n = nOf(m[1]); return /^\d+$/.test(n) ? out(`subfactorial(${n})`, `permutations of ${n} with no fixed point: !${n}`) : null; } },
    { id: "count-handshakes", re: /^(?:find |how many )?(?:the )?(?:number of )?handshakes (?:are there |happen |occur )?(?:among|between|when|if|with|at a party (?:of|with)) (\w+) people(?: each shake hands(?: once)? with (?:each other|everyone(?: else)?))?$/i,
      build: (m) => { const n = nOf(m[1]); return /^\d+$/.test(n) ? out(`binomial(${n}, 2)`, `one handshake per pair of people: C(${n}, 2)`) : null; } },

    // ---------------------------------------------------------------- complex numbers
    { id: "complex-part", re: re(`^${LEAD}(modulus|absolute value|magnitude|argument|arg|conjugate|complex conjugate|real part|imaginary part) (?:of )?(.+)$`),
      build: (m) => {
        const z = E(m[2]);
        if (!z || !/\bi\b|i\)|\di/.test(z)) return null;
        const f = { modulus: "abs", "absolute value": "abs", magnitude: "abs", argument: "arg", arg: "arg", conjugate: "conj", "complex conjugate": "conj", "real part": "re", "imaginary part": "im" }[m[1].toLowerCase()];
        return out(`${f}(${z})`, `${m[1].toLowerCase()} of the complex number ${z}`, f === "arg" ? { notes: ["The argument is the principal value, in (-pi, pi]."] } : {});
      } },
    { id: "complex-polar", re: re(`^(?:convert |write |express |put )?(?:the (?:complex )?number )?(.+?) (?:to|in|into) (?:polar|trigonometric|modulus-argument|exponential) form$`),
      build: (m) => { const z = E(m[1]); return z ? out(`polar(${z})`, `polar form r(cos t + i sin t) of ${z}: r = |z|, t = arg z`, { notes: ["The argument is the principal value, in (-pi, pi]."] }) : null; } },
    { id: "complex-polar", re: re(`^${LEAD}(?:polar|trigonometric|exponential) form (?:of )?(.+)$`),
      build: (m) => { const z = E(m[1]); return z ? out(`polar(${z})`, `polar form of ${z}: r = |z|, t = arg z`, { notes: ["The argument is the principal value, in (-pi, pi]."] }) : null; } },
    { id: "complex-unity", re: /^(?:find |what are |list )?(?:all )?(?:the )?(?:(\w+)(?:th|rd|nd|st)? roots of unity|roots of unity of (?:order|degree) (\w+))$/i,
      build: (m) => { const n = nOf(m[1] || m[2]); return /^\d+$/.test(n) && +n >= 1 && +n <= 12 ? out(`z^${n} = 1`, `solve z^${n} = 1 over the complex numbers`, { goal: "solve", variable: "z", domain: "complex" }) : null; } },
    { id: "solve-interval", re: /^(?:solve|find all solutions (?:of|to)|find (?:all )?(?:the )?(?:solutions|roots) of) (.+?=.+?),? (?:for|on|in|over|with|where|given) (?:the interval |x in |x ∈ )?(.+)$/i,
      build: (m) => {
        const eq = E(m[1]);
        if (!eq) return null;
        const iv = m[2].trim();
        let mm, a, b, cl, cr;
        if ((mm = /^([[(])\s*([^,]+?)\s*,\s*([^,]+?)\s*([\])])$/.exec(iv))) { a = mm[2]; b = mm[3]; cl = mm[1] === "["; cr = mm[4] === "]"; }
        else if ((mm = /^(.+?)\s*(<=|≤|<)\s*x\s*(<=|≤|<)\s*(.+)$/.exec(iv))) { a = mm[1]; b = mm[4]; cl = mm[2] !== "<"; cr = mm[3] !== "<"; }
        else return null;
        const A = E(a), B = E(b);
        if (!A || !B) return null;
        return out(`solvein(${eq}, x, ${A}, ${B}, ${cl ? 1 : 0}, ${cr ? 1 : 0})`, `solve ${eq} for x in ${cl ? "[" : "("}${A}, ${B}${cr ? "]" : ")"}`);
      } },
    { id: "complex-solve", re: /^solve (.+?) (?:over|in) (?:the )?(?:complex(?: numbers)?|c|ℂ)$/i,
      build: (m) => { const t = E(m[1]); return t && /=/.test(t) ? out(t, `solve ${t} over the complex numbers`, { goal: "solve", domain: "complex" }) : null; } },

    // ---------------------------------------------------------------- sequences and series
    { id: "series-first-n", re: /^(?:find |what is |compute )?(?:the )?sum of (?:the )?first (\w+) (positive |natural )?(integers|natural numbers|numbers|whole numbers|odd numbers|odd integers|even numbers|even integers|squares|perfect squares|cubes|perfect cubes)$/i,
      build: (m) => {
        const n = nOf(m[1]);
        if (!/^\d+$/.test(n)) return null;
        const kind = m[3].toLowerCase();
        const body = /odd/.test(kind) ? "2k - 1" : /even/.test(kind) ? "2k" : /square/.test(kind) ? "k^2" : /cube/.test(kind) ? "k^3" : "k";
        return out(`sum(${body}, k, 1, ${n})`, `sum of ${body} for k = 1 to ${n}`);
      } },
    { id: "series-nth-term", re: /^(?:find |what is )?(?:the )?(\w+?)(?:th|st|nd|rd)? term (?:of )?(?:the )?(arithmetic|geometric)? ?(?:sequence|progression|series)?:? ?(-?\d[\d./]*(?:\s*,\s*-?\d[\d./]*){2,})(?:\s*,?\s*(?:\.{1,3}|…))?,?$/i,
      build: (m) => {
        const xs = m[3].split(/\s*,\s*/).map(Number);
        if (xs.some((v) => !Number.isFinite(v))) return null;
        const t = m[3].split(/\s*,\s*/);
        const d = xs[1] - xs[0], r = xs[0] !== 0 ? xs[1] / xs[0] : NaN;
        const arith = xs.every((v, i) => i === 0 || Math.abs(v - xs[i - 1] - d) < 1e-12);
        const geom = Number.isFinite(r) && xs.every((v, i) => i === 0 || Math.abs(v - xs[i - 1] * r) < 1e-12 * Math.max(1, Math.abs(v)));
        const want = (m[2] || "").toLowerCase();
        const n = /^n$/i.test(m[1]) ? "n" : nOf(m[1]);
        if (n !== "n" && !/^\d+$/.test(n)) return null;
        if ((want === "arithmetic" || (!want && arith && !geom)) && arith) return out(`${t[0]} + (${n} - 1)*(${t[1]} - ${t[0]})`, `arithmetic sequence: a_n = a_1 + (n - 1)d with a_1 = ${t[0]}, d = ${t[1]} - ${t[0]}`);
        if ((want === "geometric" || (!want && geom && !arith)) && geom) return out(`${t[0]} * ((${t[1]})/(${t[0]}))^(${n} - 1)`, `geometric sequence: a_n = a_1 r^(n - 1) with a_1 = ${t[0]}, r = ${t[1]}/${t[0]}`);
        return null;
      } },
    { id: "series-finite", re: /^(?:find |what is )?(?:the )?sum of (?:the )?(?:first (\w+) terms of (?:the )?)?(?:(arithmetic|geometric) (?:series|sequence|progression):? ?|(?:series|sequence|progression):? ?)?(-?\d[\d./]*(?:\s*(?:,|\+)\s*-?\d[\d./]*){2,})(?:\s*(?:,|\+)?\s*(?:\.{1,3}|…)?)?(?:,? ?(?:to |with |for )?(\w+) terms)?$/i,
      build: (m) => {
        const n = nOf(m[1] || m[4] || "");
        if (!/^\d+$/.test(n)) return null;
        const t = m[3].split(/\s*(?:,|\+)\s*/), xs = t.map(Number);
        const d = xs[1] - xs[0], arith = xs.every((v, i) => i === 0 || Math.abs(v - xs[i - 1] - d) < 1e-12);
        // no "arithmetic"/"geometric": decided by the terms (constant difference or constant ratio)
        const kind = m[2] ? m[2].toLowerCase() : arith ? "arithmetic" : "geometric";
        if (kind === "arithmetic") {
          if (!arith) return null;
          return out(`sum(${t[0]} + (k - 1)*(${t[1]} - ${t[0]}), k, 1, ${n})`, `arithmetic series, ${n} terms: first ${t[0]}, difference ${t[1]} - ${t[0]}`);
        }
        const r = xs[1] / xs[0];
        if (!xs.every((v, i) => i === 0 || Math.abs(v - xs[i - 1] * r) < 1e-12 * Math.max(1, Math.abs(v)))) return null;
        return out(`sum(${t[0]} * ((${t[1]})/(${t[0]}))^(k - 1), k, 1, ${n})`, `geometric series, ${n} terms: first ${t[0]}, ratio ${t[1]}/${t[0]}`);
      } },
    { id: "series-infinite-geo", re: /^(?:find |what is )?(?:the )?sum (?:of )?(?:the |an )?infinite geometric (?:series|progression)(?: with)? a ?= ?([\d./-]+),? (?:and )?r ?= ?([\d./-]+)$/i,
      build: (m) => out(`sum(${m[1]} * (${m[2]})^k, k, 0, oo)`, `infinite geometric series a + ar + ar^2 + ... with a = ${m[1]}, r = ${m[2]}`) },
    { id: "series-converge", re: /^(?:does|do|is|determine (?:if|whether)) (?:the (?:series|sum) )?(?:sum|series|Σ|∑)?\s*(?:of )?(.+?) (?:converge|diverge|convergent|divergent|converges|diverges)$/i,
      build: (m) => {
        let body = m[1].replace(/^(?:sum|the sum of|the series)\s+/i, "").replace(/\s+from\s+\w\s*=\s*1\s+to\s+(?:infinity|oo|∞)$/i, "");
        const b = E(body);
        if (!b) return null;
        const v = (b.match(/\b[nk]\b/) || ["n"])[0];
        return out(`sum(${b}, ${v}, 1, oo)`, `the series sum of ${b} for ${v} = 1 to infinity`);
      } },

    // ---------------------------------------------------------------- geometry formulas
    { id: "geo-circle", re: re(`^${LEAD}(area|circumference|perimeter|diameter) (?:of )?(?:a |the )?circle (?:with|of|whose) (radius|diameter|r|d)(?: is| of| =)? ?${num}(?: ?\\w+)?$`),
      build: (m) => {
        const r = /^d/i.test(m[2]) ? `(${m[3]})/2` : m[3], q = m[1].toLowerCase();
        return out(q === "area" ? `pi*(${r})^2` : q === "diameter" ? `2*(${r})` : `2*pi*(${r})`, `${q} of a circle of radius ${r}: ${q === "area" ? "pi r^2" : q === "diameter" ? "2r" : "2 pi r"}`);
      } },
    { id: "geo-triangle", re: re(`^${LEAD}area (?:of )?(?:a |the )?triangle (?:with|whose|of) base ${num}(?: ?\\w+)? and height ${num}(?: ?\\w+)?$`),
      build: (m) => out(`(${m[1]})*(${m[2]})/2`, `area = base x height / 2`) },
    { id: "geo-heron", re: re(`^${LEAD}area (?:of )?(?:a |the )?triangle (?:with|whose|of) sides? (?:of )?(?:lengths? )?${num},? ${num},? (?:and )?${num}$`),
      build: (m) => {
        const [a, b, c] = [m[1], m[2], m[3]].map(Number);
        if (!(a + b > c && a + c > b && b + c > a)) return null;
        return out(`sqrt(((${m[1]}) + (${m[2]}) + (${m[3]}))/2 * (((${m[2]}) + (${m[3]}) - (${m[1]}))/2) * (((${m[1]}) + (${m[3]}) - (${m[2]}))/2) * (((${m[1]}) + (${m[2]}) - (${m[3]}))/2))`, `Heron's formula: sqrt(s(s - a)(s - b)(s - c)) with s the half perimeter`);
      } },
    { id: "geo-solid", re: re(`^${LEAD}(volume|surface area) (?:of )?(?:a |the )?(sphere|ball|hemisphere) (?:with|of|whose) (radius|diameter|r|d)(?: is| of| =)? ?${num}(?: ?\\w+)?$`),
      build: (m) => {
        const r = /^d/i.test(m[3]) ? `(${m[4]})/2` : m[4], vol = /vol/i.test(m[1]), hemi = /hemi/i.test(m[2]);
        if (hemi) return out(vol ? `2*pi*(${r})^3/3` : `3*pi*(${r})^2`, vol ? "hemisphere volume (2/3) pi r^3" : "hemisphere total surface area 3 pi r^2 (curved 2 pi r^2 plus the flat disc)");
        return out(vol ? `4*pi*(${r})^3/3` : `4*pi*(${r})^2`, vol ? "sphere volume (4/3) pi r^3" : "sphere surface area 4 pi r^2");
      } },
    { id: "geo-solid", re: re(`^${LEAD}(volume|surface area|lateral surface area|curved surface area) (?:of )?(?:a |the )?(?:right )?(?:circular )?(cylinder|cone) (?:with|of|whose) radius ${num}(?: ?\\w+)?,? and (?:a )?height ${num}(?: ?\\w+)?$`),
      build: (m) => {
        const [q, s, r, h] = [m[1].toLowerCase(), m[2].toLowerCase(), m[3], m[4]];
        if (s === "cylinder") return out(q === "volume" ? `pi*(${r})^2*(${h})` : /lateral|curved/.test(q) ? `2*pi*(${r})*(${h})` : `2*pi*(${r})^2 + 2*pi*(${r})*(${h})`, q === "volume" ? "cylinder volume pi r^2 h" : /lateral|curved/.test(q) ? "curved surface 2 pi r h" : "total surface 2 pi r^2 + 2 pi r h");
        return out(q === "volume" ? `pi*(${r})^2*(${h})/3` : /lateral|curved/.test(q) ? `pi*(${r})*sqrt((${r})^2 + (${h})^2)` : `pi*(${r})^2 + pi*(${r})*sqrt((${r})^2 + (${h})^2)`, q === "volume" ? "cone volume (1/3) pi r^2 h" : /lateral|curved/.test(q) ? "curved surface pi r l, slant l = sqrt(r^2 + h^2)" : "total surface pi r^2 + pi r l, slant l = sqrt(r^2 + h^2)");
      } },
    { id: "geo-cube", re: re(`^${LEAD}(volume|surface area|diagonal|space diagonal) (?:of )?(?:a |the )?cube (?:with|of|whose) (?:side|edge|side length|edge length)(?: is| of| =)? ?${num}(?: ?\\w+)?$`),
      build: (m) => { const q = m[1].toLowerCase(), s = m[2]; return out(q === "volume" ? `(${s})^3` : q === "surface area" ? `6*(${s})^2` : `sqrt(3)*(${s})`, q === "volume" ? "cube volume s^3" : q === "surface area" ? "cube surface area 6 s^2" : "cube space diagonal s sqrt(3)"); } },
    { id: "geo-box", re: re(`^${LEAD}(volume|surface area) (?:of )?(?:a |the )?(?:rectangular (?:box|prism|solid)|cuboid|box) (?:with (?:dimensions|sides|length,? width,? and height) )?${num}(?: ?\\w+)? ?(?:by|x|×|,) ?${num}(?: ?\\w+)? ?(?:by|x|×|,|and) ?${num}(?: ?\\w+)?$`),
      build: (m) => out(/vol/i.test(m[1]) ? `(${m[2]})*(${m[3]})*(${m[4]})` : `2*((${m[2]})*(${m[3]}) + (${m[2]})*(${m[4]}) + (${m[3]})*(${m[4]}))`, /vol/i.test(m[1]) ? "box volume l w h" : "box surface area 2(lw + lh + wh)") },
    { id: "geo-rect", re: re(`^${LEAD}(area|perimeter|diagonal) (?:of )?(?:a |the )?rectangle (?:with (?:length|sides|dimensions) )?${num}(?: ?\\w+)? ?(?:by|x|×|and|,)(?: width)? ?${num}(?: ?\\w+)?$`),
      build: (m) => { const q = m[1].toLowerCase(); return out(q === "area" ? `(${m[2]})*(${m[3]})` : q === "perimeter" ? `2*((${m[2]}) + (${m[3]}))` : `sqrt((${m[2]})^2 + (${m[3]})^2)`, q === "area" ? "rectangle area l w" : q === "perimeter" ? "rectangle perimeter 2(l + w)" : "rectangle diagonal sqrt(l^2 + w^2)"); } },
    { id: "geo-square", re: re(`^${LEAD}(area|perimeter|diagonal) (?:of )?(?:a |the )?square (?:with|of|whose) (?:side|side length|sides)(?: is| of| =)? ?${num}(?: ?\\w+)?$`),
      build: (m) => { const q = m[1].toLowerCase(), s = m[2]; return out(q === "area" ? `(${s})^2` : q === "perimeter" ? `4*(${s})` : `sqrt(2)*(${s})`, q === "area" ? "square area s^2" : q === "perimeter" ? "square perimeter 4s" : "square diagonal s sqrt(2)"); } },
    { id: "geo-trapezoid", re: re(`^${LEAD}area (?:of )?(?:a |the )?trapezo(?:id|ium) (?:with|whose) (?:parallel )?(?:sides|bases) ${num}(?: ?\\w+)? and ${num}(?: ?\\w+)?,? and (?:a )?height ${num}(?: ?\\w+)?$`),
      build: (m) => out(`((${m[1]}) + (${m[2]}))*(${m[3]})/2`, "trapezoid area (a + b) h / 2") },
    { id: "geo-parallelogram", re: re(`^${LEAD}area (?:of )?(?:a |the )?parallelogram (?:with|whose) base ${num}(?: ?\\w+)? and height ${num}(?: ?\\w+)?$`),
      build: (m) => out(`(${m[1]})*(${m[2]})`, "parallelogram area base x height") },
    { id: "geo-hyp", re: re(`^${LEAD}hypotenuse (?:of )?(?:a |the )?(?:right(?:[- ]angled)? )?triangle (?:with|whose) legs? (?:of )?${num}(?: ?\\w+)? and ${num}(?: ?\\w+)?$`),
      build: (m) => out(`sqrt((${m[1]})^2 + (${m[2]})^2)`, "Pythagoras: c = sqrt(a^2 + b^2)") },
    { id: "geo-leg", re: re(`^${LEAD}(?:other |missing |third )?(?:leg|side) (?:of )?(?:a |the )?right(?:[- ]angled)? triangle (?:with|whose) hypotenuse ${num}(?: ?\\w+)? and (?:one )?(?:leg|side) ${num}(?: ?\\w+)?$`),
      build: (m) => (+m[1] > +m[2] ? out(`sqrt((${m[1]})^2 - (${m[2]})^2)`, "Pythagoras: b = sqrt(c^2 - a^2)") : null) },
    { id: "geo-angles", re: re(`^${LEAD}(sum of (?:the )?interior angles|interior angle sum|(?:each|one) interior angle|(?:each|one) exterior angle|sum of (?:the )?exterior angles) (?:of|in) (?:a |an |each |one )?(regular )?([\\w -]+?)$`),
      build: (m) => {
        const n = sidesOf(m[3]);
        if (!n) return null;
        const q = m[1].toLowerCase();
        if (/sum of (?:the )?exterior/.test(q)) return out("360", "the exterior angles of any convex polygon add up to 360 degrees", { notes: ["Degrees."] });
        if (/each|one/.test(q) && /exterior/.test(q)) return out(`360/${n}`, `regular polygon: each exterior angle is 360/${n} degrees`, { notes: ["Degrees; assumes a regular polygon."] });
        if (/each|one/.test(q)) return out(`(${n} - 2)*180/${n}`, `regular polygon: each interior angle (n - 2) 180 / n degrees with n = ${n}`, { notes: ["Degrees; assumes a regular polygon."] });
        return out(`(${n} - 2)*180`, `interior angle sum (n - 2) x 180 degrees with n = ${n}`, { notes: ["Degrees."] });
      } },
    { id: "geo-cosines", re: /^(?:use )?(?:the )?law of cosines:? a ?= ?([\d.]+),? b ?= ?([\d.]+),? (?:and )?(?:angle )?c ?= ?([\d.]+) ?(?:degrees|deg|°)(?:,|\.)? (?:find|what is) (?:side )?c$/i,
      build: (m) => out(`sqrt((${m[1]})^2 + (${m[2]})^2 - 2*(${m[1]})*(${m[2]})*cos(${m[3]}*pi/180))`, `law of cosines c^2 = a^2 + b^2 - 2ab cos C with C = ${m[3]} degrees`) },
    { id: "geo-sines", re: /^(?:use )?(?:the )?law of sines:? a ?= ?([\d.]+),? (?:angle )?a ?= ?([\d.]+) ?(?:degrees|deg|°),? (?:and )?(?:angle )?b ?= ?([\d.]+) ?(?:degrees|deg|°)(?:,|\.)? (?:find|what is) (?:side )?b$/i,
      build: (m) => out(`(${m[1]})*sin(${m[3]}*pi/180)/sin(${m[2]}*pi/180)`, `law of sines b = a sin B / sin A with A = ${m[2]} and B = ${m[3]} degrees`) },
    { id: "geo-line-dist", re: /^(?:find |what is )?(?:the )?(?:perpendicular |shortest )?distance (?:from|between) (?:the )?(?:point )?\(\s*([^,()]+?)\s*,\s*([^,()]+?)\s*\) (?:to|and) (?:the )?line (.+)$/i,
      build: (m) => { const x0 = E(m[1]), y0 = E(m[2]), l = E(m[3]); return x0 && y0 && l && /[xy]/.test(l) ? out(`linedist(${x0}, ${y0}, ${l})`, `distance from (${x0}, ${y0}) to the line ${l}: |a x0 + b y0 + c| / sqrt(a^2 + b^2)`) : null; } },
    { id: "geo-circle-eq", re: re(`^${LEAD}(?:centre|center)(?: and radius|,? radius)? (?:of )?(?:the circle )?(.+)$`),
      build: (m) => { const c = E(m[1]); return c && /x/.test(c) && /y/.test(c) ? out(`circle(${c})`, `complete the square in x and y to read off the centre and radius of ${c}`) : null; } },
    { id: "geo-circle-eq", re: re(`^${LEAD}radius (?:and (?:centre|center) )?(?:of )?(?:the circle )?(.+)$`),
      build: (m) => { const c = E(m[1]); return c && /x/.test(c) && /y/.test(c) && /=/.test(c) ? out(`circle(${c})`, `complete the square in x and y to read off the centre and radius of ${c}`) : null; } },

    // ---------------------------------------------------------------- trig and angle units
    { id: "angle-convert", re: /^(?:convert )?(.+?) ?(radians?|rad|degrees?|deg|°) (?:to|in|into) (degrees?|deg|radians?|rad)$/i,
      build: (m) => {
        const v = E(m[1]);
        if (!v) return null;
        const fromDeg = /^d|°/i.test(m[2]), toDeg = /^d/i.test(m[3]);
        if (fromDeg === toDeg) return null;
        return toDeg ? out(`(${v})*180/pi`, `${v} radians x 180/pi`, { notes: ["The answer is in degrees."] }) : out(`(${v})*pi/180`, `${v} degrees x pi/180`, { notes: ["The answer is in radians."] });
      } },

    // ---------------------------------------------------------------- logs, growth and money
    { id: "log-condense", re: /^(?:condense|combine|contract|write as a single (?:log|logarithm)|express as a single (?:log|logarithm))(?: the expression)?:? (.+)$/i,
      build: (m) => { const t = E(m[1]); return t && /log|ln/.test(t) ? out(t, `combine ${t} into a single logarithm`, { goal: "condense" }) : null; } },
    { id: "log-expand", re: /^(?:expand|write as a sum of logarithms)(?: the (?:logarithm|log|expression))?:? (.+)$/i,
      build: (m) => { const t = E(m[1]); return t && /log|ln/.test(t) ? out(t, `expand ${t} with the logarithm laws`, { goal: "expand" }) : null; } },
    { id: "compound", re: /^(?:find (?:the )?)?compound interest(?: on)?:? \$?([\d,.]+) (?:dollars )?at ([\d.]+) ?%(?: (?:per year|a year|annually|p\.?a\.?))?(?: compounded (annually|yearly|semi-?annually|quarterly|monthly|weekly|daily|continuously))? for ([\d.]+) years?$/i,
      build: (m) => {
        const P = m[1].replace(/,/g, ""), r = m[2], t = m[4], how = (m[3] || "annually").toLowerCase();
        if (how === "continuously") return out(`${P}*e^(${r}/100*${t})`, `continuous compounding: A = P e^(rt) with P = ${P}, r = ${r}%, t = ${t}`);
        const n = { annually: 1, yearly: 1, semiannually: 2, "semi-annually": 2, quarterly: 4, monthly: 12, weekly: 52, daily: 365 }[how];
        return out(`${P}*(1 + ${r}/100/${n})^(${n}*${t})`, `A = P (1 + r/n)^(nt) with P = ${P}, r = ${r}%, n = ${n} per year, t = ${t}`, { notes: ["This is the final amount; the interest earned is this minus the principal."] });
      } },
    { id: "half-life", re: /^(?:half[- ]life:? )?(?:a (?:sample|substance) of )?([\d.]+) ?(?:grams|g|mg|kg|units|atoms)?,? (?:with a |has a |and a )?half[- ]life (?:of |is )?([\d.]+) ?(years?|days?|hours?|minutes?|seconds?)?,? (?:how much (?:is left|remains) after|amount (?:left |remaining )?after|what remains after) ([\d.]+) ?(years?|days?|hours?|minutes?|seconds?)?$/i,
      build: (m) => out(`${m[1]}*(1/2)^(${m[4]}/${m[2]})`, `half-life decay: A = A0 (1/2)^(t / T) with A0 = ${m[1]}, T = ${m[2]}, t = ${m[4]}`) },
    { id: "depreciation", re: /^(?:a|the) (?:car|machine|computer|truck|phone|house|asset|item)? ?(?:worth \$?([\d,.]+) )?(?:depreciates|loses value|decreases|declines) (?:by |at )?([\d.]+) ?% (?:per|a|each) year(?: from \$?([\d,.]+))?[.,]? (?:what is its |find its |its )?value after ([\d.]+) years?$/i,
      build: (m) => { const V = (m[1] || m[3] || "").replace(/,/g, ""); return V ? out(`${V}*(1 - ${m[2]}/100)^${m[4]}`, `value = V (1 - r)^t with V = ${V}, r = ${m[2]}%, t = ${m[4]}`) : null; } },
    { id: "growth", re: /^(?:a )?population of ([\d,.]+) (?:grows|increases) (?:by |at )?([\d.]+) ?% (?:per|a|each) year[.,]? (?:what is (?:the|its) )?(?:population )?(?:after|in) ([\d.]+) years?$/i,
      build: (m) => out(`${m[1].replace(/,/g, "")}*(1 + ${m[2]}/100)^${m[3]}`, `P = P0 (1 + r)^t with P0 = ${m[1]}, r = ${m[2]}%, t = ${m[3]}`) },

    // ---------------------------------------------------------------- polynomials
    { id: "poly-divide", re: /^(?:divide|use (?:long|synthetic) division to divide) (.+?) by (.+)$/i,
      build: (m) => { const a = E(m[1]), b = E(m[2]); return a && b && /[a-z]/.test(a + b) ? out(`polydiv(${a}, ${b})`, `polynomial long division of ${a} by ${b}`) : null; } },
    { id: "poly-remainder", re: /^(?:find |what is )?(?:the )?(remainder|quotient) (?:when|of) (.+?) (?:is )?divided by (.+)$/i,
      build: (m) => {
        const a = E(m[2]), b = E(m[3]);
        if (!a || !b) return null;
        let mm;
        if (!/[a-z]/i.test(a + b)) return null; // integers: the existing remainder pattern
        if ((mm = /^(\d+)\^(\d+)$/.exec(a)) && /^\d+$/.test(b)) return out(`powmod(${mm[1]}, ${mm[2]}, ${b})`, `${a} mod ${b} by fast modular exponentiation`);
        return out(m[1].toLowerCase() === "remainder" ? `polyrem(${a}, ${b})` : `polydiv(${a}, ${b})`, `polynomial division of ${a} by ${b}${m[1].toLowerCase() === "remainder" ? ": the remainder" : ""}`);
      } },
    { id: "powmod", re: /^(?:find |what is )?(?:the )?remainder (?:when|of) (\d+) ?\^ ?(\d+) (?:is )?divided by (\d+)$/i,
      build: (m) => out(`powmod(${m[1]}, ${m[2]}, ${m[3]})`, `${m[1]}^${m[2]} mod ${m[3]} by fast modular exponentiation`) },
    { id: "poly-coeff", re: re(`^${LEAD}coefficient (?:of )?([a-z](?:\\^\\d+)?) in (?:the expansion of )?(.+)$`),
      build: (m) => { const p = E(m[2]); return p ? out(`coeff(${p}, ${m[1]})`, `the coefficient of ${m[1]} when ${p} is expanded`) : null; } },
    { id: "poly-vieta", re: re(`^${LEAD}(sum|product) of (?:the |all )?(?:roots|zeros|zeroes|solutions) (?:of )?(?:the (?:polynomial|equation) )?(.+)$`),
      build: (m) => { const p = E(m[2]); return p && /[a-z]/.test(p) ? out(`${/sum/i.test(m[1]) ? "rootsum" : "rootprod"}(${p})`, `Vieta's formulas: ${m[1].toLowerCase()} of all roots of ${p} (complex roots and multiplicity included)`) : null; } },
    { id: "poly-disc", re: re(`^${LEAD}discriminant (?:of )?(?:the (?:quadratic|polynomial|equation) )?(.+)$`),
      build: (m) => { const p = E(m[1].replace(/\s*=\s*0$/, "")); return p ? out(`discriminant(${p})`, `discriminant of ${p}`) : null; } },
    { id: "poly-vertex", re: re(`^${LEAD}(?:vertex|turning point) (?:of )?(?:the (?:parabola|quadratic|graph|function) )?(?:(?:y|f\\(x\\)) ?= ?)?(.+)$`),
      build: (m) => { const p = E(m[1]); return p ? out(`vertex(${p})`, `vertex of the parabola y = ${p} at x = -b/(2a)`) : null; } },
    { id: "poly-gcd", re: re(`^${LEAD}(?:gcd|greatest common divisor) of (?:the polynomials )?(.+?) and (.+)$`),
      build: (m) => { const a = E(m[1]), b = E(m[2]); return a && b && /[a-z]/.test(a + b) ? out(`polygcd(${a}, ${b})`, `monic greatest common divisor of ${a} and ${b}`) : null; } },

    // ---------------------------------------------------------------- number theory
    { id: "modinv", re: /^(?:find |what is |compute )?(?:the )?(?:modular |multiplicative )?inverse (?:of )?(-?\d+) (?:mod|modulo|\(mod) (\d+)\)?$/i,
      build: (m) => out(`modinv(${m[1]}, ${m[2]})`, `the x in 0..${+m[2] - 1} with ${m[1]} x = 1 (mod ${m[2]})`) },
    { id: "to-base", re: /^(?:convert |write |express )?(\d+) (?:\(?(?:in )?(?:base 10|decimal)\)? )?(?:to|in|into) (binary|octal|hexadecimal|hex|ternary|base[- ]?\d+)$/i,
      build: (m) => { const b = baseOf(m[2]); return b && b >= 2 && b <= 36 ? out(`tobase(${m[1]}, ${b})`, `${m[1]} written in base ${b}`) : null; } },
    { id: "from-base", re: /^(?:convert |what is )?(?:the )?(?:number )?([0-9a-z]+)(?:_(\d+))? (?:from |in )?(binary|octal|hexadecimal|hex|ternary|base[- ]?\d+)? ?(?:to|in|into) (?:decimal|base[- ]?10)$/i,
      build: (m) => {
        const b = m[2] ? Number(m[2]) : m[3] && baseOf(m[3]);
        if (!b || b < 2 || b > 36) return null;
        const digits = m[1].toLowerCase();
        const vals = [...digits].map((c) => parseInt(c, 36));
        if (vals.some((v) => !(v < b))) return null;
        const terms = vals.map((v, i) => `${v}*${b}^${vals.length - 1 - i}`);
        return out(terms.join(" + "), `positional value of ${digits} in base ${b}: ${terms.join(" + ")}`);
      } },
    { id: "divisor-count", re: /^(?:find |what is |how many )?(?:the )?(number|sum|count) of (?:the )?(?:positive )?(?:divisors|factors) (?:of|does) (\d+)(?: have)?$/i,
      build: (m) => out(`${/sum/i.test(m[1]) ? "divisorsum" : "numdivisors"}(${m[2]})`, `${/sum/i.test(m[1]) ? "sum" : "number"} of the positive divisors of ${m[2]}`) },
    { id: "divisor-count", re: /^how many (?:positive )?(?:divisors|factors) does (\d+) have$/i,
      build: (m) => out(`numdivisors(${m[1]})`, `number of positive divisors of ${m[1]}`) },
    { id: "last-digits", re: /^(?:find |what is |what are )?(?:the )?last (?:(\w+) )?digits? of (\d+) ?\^ ?(\d+)$/i,
      build: (m) => { const k = m[1] ? nOf(m[1]) : "1"; return /^\d+$/.test(k) && +k >= 1 && +k <= 50 ? out(`powmod(${m[2]}, ${m[3]}, 10^${k})`, `last ${k === "1" ? "digit" : k + " digits"}: ${m[2]}^${m[3]} mod 10^${k}`, { notes: +k > 1 ? ["Leading zeros of the last digits are not shown."] : [] }) : null; } },
    { id: "nth-prime", re: /^(?:find |what is )?(?:the )?(\d+)(?:st|nd|rd|th) prime(?: number)?$/i,
      build: (m) => out(`nthprime(${m[1]})`, `the ${m[1]}th prime (2 is the first)`) },

    // ---------------------------------------------------------------- calculus phrasing
    { id: "tangent-slope", re: /^(?:find |what is )?(?:the )?slope (?:of )?(?:the )?tangent(?: line)? (?:to|of) (?:the (?:curve|graph) )?(?:y ?= ?|f\(x\) ?= ?)?(.+?) at (?:the point )?x ?= ?(.+)$/i,
      build: (m) => { const f = E(m[1]), a = E(m[2]); return f && a && !/x/.test(a) ? out(`diffat(${f}, x, ${a})`, `slope = f'(${a}) for f(x) = ${f}`) : null; } },
    { id: "derivative-at", re: /^(?:find |what is |evaluate )?(?:the )?(?:value of the )?derivative of (?:y ?= ?|f\(x\) ?= ?)?(.+?) at (?:the point )?x ?= ?(.+)$/i,
      build: (m) => { const f = E(m[1]), a = E(m[2]); return f && a && !/x/.test(a) ? out(`diffat(${f}, x, ${a})`, `f'(${a}) for f(x) = ${f}`) : null; } },
    { id: "derivative-at", re: /^(?:find |what is |evaluate )?f'\((.+?)\) (?:if|when|given|where|for) f\(x\) ?= ?(.+)$/i,
      build: (m) => { const f = E(m[2]), a = E(m[1]); return f && a && !/x/.test(a) ? out(`diffat(${f}, x, ${a})`, `f'(${a}) for f(x) = ${f}`) : null; } },
    { id: "gradient", re: re(`^${LEAD}gradient (?:vector )?(?:of )?(.+)$`),
      build: (m) => { const f = E(m[1]); if (!f) return null; const vs = ["x", "y", "z"].filter((v) => new RegExp(`\\b${v}\\b|${v}(?=[\\^*+\\-/) ]|$)`).test(f)); return vs.length >= 2 ? out(`grad(${f}, ${vs.join(", ")})`, `gradient: the partial derivatives of ${f} with respect to ${vs.join(", ")}`) : null; } },
    { id: "double-integral", re: /^(?:find |evaluate |compute )?(?:the )?double integral (?:of )?(.+?) over ([\d.-]+) ?<= ?x ?<= ?([\d.-]+),? (?:and )?([\d.-]+) ?<= ?y ?<= ?([\d.-]+)$/i,
      build: (m) => { const f = E(m[1]); return f ? out(`dblint(${f}, x, ${m[2]}, ${m[3]}, y, ${m[4]}, ${m[5]})`, `iterated integral of ${f} over x in [${m[2]}, ${m[3]}], y in [${m[4]}, ${m[5]}]`) : null; } },

    // ---------------------------------------------------------------- arithmetic phrasing
    { id: "round", re: /^round (.+?) to (?:the nearest )?(\w+) (?:decimal places?|dp|places?|decimals?)$/i,
      build: (m) => { const x = E(m[1]), d = nOf(m[2]); return x && /^\d+$/.test(d) ? out(`round(${x}, ${d})`, `round ${x} to ${d} decimal place${d === "1" ? "" : "s"} (halves away from zero)`) : null; } },
    { id: "round", re: /^round (.+?) to the nearest (whole number|integer|unit|one|ten|hundred|thousand|tenth|hundredth|thousandth)$/i,
      build: (m) => { const x = E(m[1]); const d = { "whole number": 0, integer: 0, unit: 0, one: 0, ten: -1, hundred: -2, thousand: -3, tenth: 1, hundredth: 2, thousandth: 3 }[m[2].toLowerCase()]; return x ? out(`round(${x}, ${d})`, `round ${x} to the nearest ${m[2]} (halves away from zero)`) : null; } },
    { id: "as-fraction", re: /^(?:write |express |convert )?(\d*\.\d+(?:\.\.\.|…)?) (?:as|to|into) (?:a )?(?:fraction|ratio)(?: in (?:simplest|lowest) (?:form|terms))?$/i,
      build: (m) => {
        const r = repeatingDecimal(m[1]);
        if (r) {
          const a = r.pre.length, b = r.block.length;
          const whole = `${r.pre}${r.block}`.replace(/^0+(?=\d)/, "") || "0", head = (r.pre || "0").replace(/^0+(?=\d)/, "");
          return out(`${r.ip} + (${whole} - ${head})/(10^${a}*(10^${b} - 1))`, `repeating decimal ${r.ip}.${r.pre}(${r.block}) repeating: ${r.ip} + (${whole} - ${head}) / (10^${a} (10^${b} - 1))`, { notes: [`Read as ${r.ip}.${r.pre}${r.block}${r.block}${r.block}... with "${r.block}" repeating forever.`] });
        }
        if (/\.\.\.|…/.test(m[1])) return null;
        return out(m[1], `${m[1]} as an exact fraction`);
      } },

    // ---------------------------------------------------------------- word problems
    { id: "unit-rate", re: /^if (\S+) (\w+) costs? \$?([\d.]+)(?: dollars)?,? how much (?:do|does|would|will) (\S+) (?:\2|of them) cost$/i,
      build: (m) => { const a = nOf(m[1]), c = nOf(m[4]); return /^[\d.]+$/.test(a) && /^[\d.]+$/.test(c) ? out(`${m[3]}/${a}*${c}`, `unit price ${m[3]}/${a} per ${m[2].replace(/s$/, "")}, times ${c}`) : null; } },
    { id: "number-op", re: /^what number (increased by|plus|decreased by|minus|multiplied by|times|divided by) (\S+) (?:is|equals|gives) (\S+)$/i,
      build: (m) => {
        const op = m[1].toLowerCase(), a = E(m[2]), b = E(m[3]);
        if (!a || !b) return null;
        const lhs = /increased|plus/.test(op) ? `x + ${a}` : /decreased|minus/.test(op) ? `x - ${a}` : /multiplied|times/.test(op) ? `${a}*x` : `x/${a}`;
        return out(`${lhs} = ${b}`, `let the number be x: ${lhs} = ${b}`, { goal: "solve", variable: "x" });
      } },
    { id: "consecutive-product", re: /^(?:find )?(?:two|2) consecutive (even |odd |positive )?(?:integers|numbers|whole numbers) (?:whose|with a|that have a) product (?:is |of )?(\d+)$/i,
      build: (m) => {
        const kind = (m[1] || "").trim().toLowerCase();
        const step = kind === "even" || kind === "odd" ? 2 : 1;
        if (kind === "even" || kind === "odd") return null; // parity needs an integer constraint the solver does not take
        return out(`a*b = ${m[2]}, b = a + ${step}`, `let the integers be a and b = a + ${step}: a b = ${m[2]}`, { goal: "solve" });
      } },
    { id: "square-side", re: /^the area of a square is ([\d.]+)(?: \w+)?[.,]? (?:find|what is) (?:its|the) side(?: length)?$/i,
      build: (m) => out(`sqrt(${m[1]})`, `side = sqrt(area), the positive root of s^2 = ${m[1]}`) },
    { id: "rect-width", re: /^(?:a|the) rectangle has (?:a )?perimeter (?:of )?([\d.]+) and (?:a )?length (?:of )?([\d.]+)[.,]? (?:find|what is) (?:its|the) width$/i,
      build: (m) => out(`2*(${m[2]} + w) = ${m[1]}`, `perimeter 2(l + w) = ${m[1]} with l = ${m[2]}`, { goal: "solve", variable: "w" }) },
    { id: "rect-width", re: /^(?:a|the) rectangle has (?:an )?area (?:of )?([\d.]+) and (?:a )?length (?:of )?([\d.]+)[.,]? (?:find|what is) (?:its|the) width$/i,
      build: (m) => out(`(${m[1]})/(${m[2]})`, `width = area / length`) },
  ];
}

// Sentence tails that only restate the question ("... . find the numbers")
export const TAIL = /[.,]?\s*(?:find|what (?:are|is)|determine) (?:the|both) (?:two )?numbers?$/i;
