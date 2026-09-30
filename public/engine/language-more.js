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

// a count said in words: "a dozen", "a pair of", "one", "7"
const WN = (s) => { const t = String(s || "").toLowerCase().trim(); if (/^(?:a|an|one|each)$/.test(t)) return 1; if (/^(?:a )?dozen$/.test(t)) return 12; if (/^(?:a )?pair(?: of)?$/.test(t)) return 2;
  if (WORD_NUM[t] !== undefined) return WORD_NUM[t]; return /^\d+(?:\.\d+)?$/.test(t) ? Number(t) : null; };
const FRACTION_WORD = { half: [1, 2], "a half": [1, 2], "one half": [1, 2], "a third": [1, 3], "one third": [1, 3], "two thirds": [2, 3], "a quarter": [1, 4], "one quarter": [1, 4], "three quarters": [3, 4], "a fourth": [1, 4], "a fifth": [1, 5], "two fifths": [2, 5], "three fifths": [3, 5], "a tenth": [1, 10] };
const stem = (w) => String(w).toLowerCase().replace(/(?:es|s)$/, "");
const AMT = String.raw`\$?(\d+(?:\.\d+)?)(?: dollars?| bucks| euros?| pounds?| usd)?`;
const WNUM = String.raw`(-?\d+(?:\.\d+)?(?:\/\d+(?:\.\d+)?)?)`;
const NUMERIC = (t) => !!t && !/[a-z=<>]/i.test(t.replace(/sqrt|pi|cbrt/g, ""));
const isPrimeN = (n) => { if (n < 2) return false; for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; };
const ROMAN = { i: 1, v: 5, x: 10, l: 50, c: 100, d: 500, m: 1000 };
const SCALE_ZEROS = { ten: 1, hundred: 2, thousand: 3, million: 6, billion: 9, trillion: 12, quadrillion: 15 };
function everydayPatterns({ E, out, WN }) {
  const two = (a, b) => { const x = E(a), y = E(b); return NUMERIC(x) && NUMERIC(y) ? [x, y] : null; };
  return [
    // plain verbs over two numbers: "add 1/2 and 1/3", "subtract 1/4 from 3/4", "multiply 2/3 by 6", "divide 3 by 1/2"
    { id: "verb-arith", re: /^(add|sum) (.+?) (?:and|to|with|plus) (.+)$/i, build: (m) => { const p = two(m[2], m[3]); return p ? out(`(${p[0]}) + (${p[1]})`, `${p[0]} + ${p[1]}`) : null; } },
    { id: "verb-arith", re: /^(?:subtract|take|take away|deduct) (.+?) from (.+)$/i, build: (m) => { const p = two(m[1], m[2]); return p ? out(`(${p[1]}) - (${p[0]})`, `${p[1]} - ${p[0]}`) : null; } },
    { id: "verb-arith", re: /^multiply (.+?) (?:by|and|with|times) (.+)$/i, build: (m) => { const p = two(m[1], m[2]); return p ? out(`(${p[0]}) * (${p[1]})`, `${p[0]} x ${p[1]}`) : null; } },
    { id: "verb-arith", re: /^divide (.+?) by (.+)$/i, build: (m) => { const p = two(m[1], m[2]); return p ? out(`(${p[0]}) / (${p[1]})`, `${p[0]} / ${p[1]}`) : null; } },
    { id: "fraction-of", re: new RegExp(String.raw`^(?:what is |find |calculate )?(\d+\/\d+) of ${WNUM}$`, "i"), build: (m) => out(`(${m[1]}) * (${m[2]})`, `${m[1]} of ${m[2]}: ${m[1]} x ${m[2]}`) },
    { id: "compare", re: /^(?:which is (bigger|larger|greater|smaller|less|more)|which (?:number|fraction) is (bigger|larger|greater|smaller))[,:]? (.+?) or (.+)$/i,
      build: (m) => { const p = two(m[3], m[4]); if (!p) return null; const big = /bigger|larger|greater|more/i.test(m[1] || m[2]);
        return out(`${big ? "max" : "min"}(${p[0]}, ${p[1]})`, `the ${big ? "larger" : "smaller"} of ${p[0]} and ${p[1]}`); } },
    { id: "mixed-number", re: /^(?:convert |write |express |change |turn )?(\d+) (\d+)\/(\d+) (?:to|as|into) (?:an )?(?:improper fraction|fraction|a fraction)$/i,
      build: (m) => (+m[2] < +m[3] ? out(`${m[1]} + ${m[2]}/${m[3]}`, `${m[1]} ${m[2]}/${m[3]} = (${m[1]} x ${m[3]} + ${m[2]})/${m[3]}`) : null) },
    // percent word forms
    { id: "percent-whole", re: new RegExp(String.raw`^${WNUM} is ${WNUM} ?(?:%|percent) of what(?: number)?$`, "i"), build: (m) => (+m[2] ? out(`${m[1]}/(${m[2]}/100)`, `${m[1]} is ${m[2]}% of the whole: ${m[1]} / (${m[2]}/100)`) : null) },
    { id: "out-of-percent", re: new RegExp(String.raw`^(?:what (?:percent|percentage) is |express )?${WNUM} out of ${WNUM}(?: as a (?:percent|percentage)| in percent| as percent)$`, "i"), build: (m) => out(`${m[1]}/${m[2]}*100`, `${m[1]} out of ${m[2]} as a percent`, { notes: ["The answer is in percent."] }) },
    { id: "out-of-percent", re: new RegExp(String.raw`^what (?:percent|percentage) is ${WNUM} out of ${WNUM}$`, "i"), build: (m) => out(`${m[1]}/${m[2]}*100`, `${m[1]} out of ${m[2]} as a percent`, { notes: ["The answer is in percent."] }) },
    { id: "out-of-percent", re: new RegExp(String.raw`^(?:i |you |she |he |they |we )?(?:scored|got|get|scores|gets|answered|made) ${WNUM} out of ${WNUM}(?: (?:on|in) (?:the |a |my )?(?:test|exam|quiz))?[,.]? what (?:percent|percentage)(?: is that| did (?:i|you|she|he|they|we) get)?$`, "i"),
      build: (m) => (+m[1] <= +m[2] ? out(`${m[1]}/${m[2]}*100`, `${m[1]} out of ${m[2]} as a percent`, { notes: ["The answer is in percent."] }) : null) },
    { id: "change-from-to", re: new RegExp(String.raw`^(?:an? |the )?[a-z ]*? (?:grows|grew|goes|went|rises|rose|increases|increased|falls|fell|drops|dropped|decreases|decreased|changes|changed) from ${WNUM} to ${WNUM}[,.]? what is the (?:percentage|percent) (increase|decrease|change)$`, "i"),
      build: (m) => { const up = +m[2] > +m[1], k = m[3].toLowerCase(); if ((k === "increase" && !up) || (k === "decrease" && up)) return null;
        return out(k === "decrease" ? `(${m[1]} - ${m[2]})/${m[1]}*100` : `(${m[2]} - ${m[1]})/${m[1]}*100`, `percent ${k} from ${m[1]} to ${m[2]}`, { notes: ["The answer is in percent."] }); } },
    { id: "percent-chain", re: new RegExp(String.raw`^(?:an? |the )?(?:price|value|number|salary|amount|cost|population|wage) (?:of )?${WNUM} (?:is )?(increased|decreased|raised|reduced|cut|lowered) by ${WNUM} ?(?:%|percent)(?:,)? and then (increased|decreased|raised|reduced|cut|lowered) by ${WNUM} ?(?:%|percent)(?:[,.]? what is the (?:new|final|resulting) (?:price|value|number|amount|cost))?$`, "i"),
      build: (m) => { const f = (w, p) => `(1 ${/increased|raised/i.test(w) ? "+" : "-"} ${p}/100)`; return out(`${m[1]}*${f(m[2], m[3])}*${f(m[4], m[5])}`, `${m[1]} x ${f(m[2], m[3])} x ${f(m[4], m[5])}: each change applies to the new value`); } },
    // discount / sale price: "X% off Y", "Y with X% off", "sale price of $Y with X% discount"
    { id: "percent-off", re: new RegExp(String.raw`^(?:what is |what's |find |calculate )?(?:the )?(?:sale |discounted |final )?price of \$?${WNUM} (?:with |at |after )?${WNUM} ?(?:%|percent) (?:off|discount)$`, "i"),
      build: (m) => out(`${m[1]}*(1 - ${m[2]}/100)`, `${m[2]}% off ${m[1]}: ${m[1]} x (1 - ${m[2]}/100)`) },
    { id: "percent-off", re: new RegExp(String.raw`^\$?${WNUM} (?:with |at |minus )${WNUM} ?(?:%|percent) (?:off|discount)$`, "i"),
      build: (m) => out(`${m[1]}*(1 - ${m[2]}/100)`, `${m[2]}% off ${m[1]}: ${m[1]} x (1 - ${m[2]}/100)`) },
    { id: "percent-off", re: new RegExp(String.raw`^(?:what is |what's )?${WNUM} ?(?:%|percent) (?:off(?: of)?|discount(?:ed)?(?: (?:from|on|off))?) \$?${WNUM}$`, "i"),
      build: (m) => out(`${m[2]}*(1 - ${m[1]}/100)`, `${m[1]}% off ${m[2]}: ${m[2]} x (1 - ${m[1]}/100)`) },
    // "what number added to 15 gives 42"
    { id: "what-number", re: new RegExp(String.raw`^what number (added to|plus|subtracted from|multiplied by|times|divided by) ${WNUM} (?:gives|makes|equals|is|results in) ${WNUM}$`, "i"),
      build: (m) => { const op = m[1].toLowerCase(), eq = /added|plus/.test(op) ? `x + ${m[2]} = ${m[3]}` : /subtracted/.test(op) ? `${m[2]} - x = ${m[3]}` : /multiplied|times/.test(op) ? `${m[2]}*x = ${m[3]}` : `x/${m[2]} = ${m[3]}`;
        return { math: eq, goal: "solve", variable: "x", interpretation: `let x be the number: ${eq}` }; } },
    { id: "solve-and", re: /^solve (.+?=.+?) and (.+?=.+?)(?: for ([a-z]))?$/i,
      build: (m) => { const a = E(m[1]), b = E(m[2]); if (!a || !b || (a.match(/=/g) || []).length !== 1 || (b.match(/=/g) || []).length !== 1) return null;
        return { math: `${a}, ${b}`, goal: "solve", ...(m[3] ? { variable: m[3] } : {}), interpretation: `the system ${a}, ${b}` }; } },
    { id: "substitute", re: /^(?:if|given|given that|suppose) ([a-z]) ?= ?(.+?),? and ([a-z]) ?= ?(-?[\d./]+),? (?:then )?(?:what is|find|what's|evaluate|compute) \1$/i,
      build: (m) => { const body = E(m[2]); if (!body || /[=<>]/.test(body) || m[1] === m[3]) return null; return out(body.replace(new RegExp(`(?<![A-Za-z_])${m[3]}(?![A-Za-z_(])`, "g"), `(${m[4]})`), `${m[1]} = ${body} with ${m[3]} = ${m[4]}`); } },
    { id: "zeros-in", re: /^how many zeros? (?:are )?(?:there )?in (?:a |one )?(ten|hundred|thousand|million|billion|trillion|quadrillion)$/i,
      build: (m) => out(String(SCALE_ZEROS[m[1].toLowerCase()]), `one ${m[1].toLowerCase()} is 1 followed by ${SCALE_ZEROS[m[1].toLowerCase()]} zeros (10^${SCALE_ZEROS[m[1].toLowerCase()]})`) },
    // sequences given by first term and ratio / difference
    { id: "seq-term", re: /^(?:what is |find )?(?:the )?(\d+)(?:st|nd|rd|th) term of (?:a|an|the) (geometric|arithmetic) (?:sequence|progression) (?:with|whose) first term (?:is )?(-?[\d./]+),? and (?:common )?(ratio|difference) (?:is )?(-?[\d./]+)$/i,
      build: (m) => { const geo = /geo/i.test(m[2]); if (geo !== /ratio/i.test(m[4]) || +m[1] < 1) return null; return out(geo ? `${m[3]}*(${m[5]})^(${m[1]} - 1)` : `${m[3]} + (${m[1]} - 1)*(${m[5]})`, geo ? `a r^(n - 1) with a = ${m[3]}, r = ${m[5]}, n = ${m[1]}` : `a + (n - 1) d with a = ${m[3]}, d = ${m[5]}, n = ${m[1]}`); } },
    // finite series written out: "2 + 5 + 8 + ... + 32", "1 + 2 + 4 + ... + 512"
    { id: "finite-series", re: /^(?:(?:find |what is |compute |calculate )?(?:the )?sum of (?:the )?(?:finite )?(?:arithmetic |geometric )?(?:series|sequence)?:? ?)?((?:-?\d+(?:\.\d+)?\s*\+\s*){2,}-?\d+(?:\.\d+)?)\s*\+\s*(?:\.\.\.|…)\s*\+\s*(-?\d+(?:\.\d+)?)$/i,
      build: (m) => finiteSeries(m[1].split(/\s*\+\s*/).map(Number), +m[2], out) },
    // the same series listed with commas: "sum of the arithmetic series 3, 7, 11, ..., 99"
    { id: "finite-series", re: /^(?:(?:find |what is |compute |calculate )?(?:the )?sum of (?:the )?(?:finite )?(?:arithmetic |geometric )?(?:series|sequence|terms|numbers)?:? ?)((?:-?\d+(?:\.\d+)?\s*,\s*){2,}-?\d+(?:\.\d+)?)\s*,?\s*(?:\.\.\.|…)\s*,?\s*(-?\d+(?:\.\d+)?)$/i,
      build: (m) => finiteSeries(m[1].split(/\s*,\s*/).map(Number), +m[2], out) },
    // "sum of 2^k for k from 0 to 10", "sum of 1/n^2 from n = 1 to infinity"
    { id: "sum-notation", re: /^(?:find |what is |compute |calculate |evaluate )?(?:the )?sum (?:of )?(.+?) (?:from|for|as|where|with) (?:([a-z]) ?(?:=|from|runs from|goes from|going from) ?)?(-?\d+) (?:to|up to|through) (infinity|oo|∞|-?\d+)$/i,
      build: (m) => { const f = E(m[1]); if (!f) return null; const vs = [...new Set(f.replace(/sqrt|cbrt|sin|cos|tan|log|ln|exp|pi|abs/g, "").match(/[a-z]/g) || [])];
        const v = m[2] || (vs.length === 1 ? vs[0] : null); if (!v || (vs.length && !vs.every((x) => x === v))) return null; const hi = /inf|oo|∞/i.test(m[4]) ? "oo" : m[4];
        return out(`sum(${f}, ${v}, ${m[3]}, ${hi})`, `sum of ${f} for ${v} = ${m[3]} to ${hi === "oo" ? "infinity" : hi}`); } },
    { id: "sum-notation", re: /^(?:find |what is |compute |calculate |evaluate )?(?:the )?sum (?:from|for) ([a-z]) ?= ?(-?\d+) to (infinity|oo|∞|-?\d+) of (.+)$/i,
      build: (m) => { const f = E(m[4]); if (!f) return null; const hi = /inf|oo|∞/i.test(m[3]) ? "oo" : m[3]; return out(`sum(${f}, ${m[1]}, ${m[2]}, ${hi})`, `sum of ${f} for ${m[1]} = ${m[2]} to ${hi === "oo" ? "infinity" : hi}`); } },
    // "lim x->infinity of (1 + 1/x)^x"
    { id: "limit-arrow", re: /^lim(?:it)?_?\s*\(?([a-z])\s*(?:->|→|approaches|goes to|tends to)\s*(-?(?:\d+(?:\.\d+)?|infinity|inf|oo|∞|pi))\)?\s+(?:of\s+)?(.+)$/i,
      build: (m) => { const f = E(m[3]); if (!f) return null; const a = /^(?:infinity|inf|oo|∞)$/i.test(m[2]) ? "oo" : /^-(?:infinity|inf|oo|∞)$/i.test(m[2]) ? "-oo" : m[2];
        return { math: `lim_(${m[1]}->${a}) (${f})`, goal: "evaluate", interpretation: `limit of ${f} as ${m[1]} -> ${a}` }; } },
    { id: "inverse-trig-degrees", re: /^(.+?) in degrees$/i,
      build: (m) => { const f = E(m[1]); if (!f || !/^(?:arcsin|arccos|arctan|asin|acos|atan)\(/.test(f) || /[a-z]/i.test(f.replace(/arcsin|arccos|arctan|asin|acos|atan|sqrt|pi/g, ""))) return null;
        return out(`(${f})*180/pi`, `${f} converted to degrees`, { notes: ["The answer is in degrees."] }); } },
    { id: "double-time", re: /^how (?:long|many years) (?:does it take |will it take |would it take )?(?:for )?(?:money|an investment|my money|your money|a sum|savings|it)? ?to (double|triple|quadruple)(?: (?:money|an investment|your money|my money|it))? (?:at|with|earning) (\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:interest|per year|a year|annually|per annum|annual interest))*(?:,? compounded (?:annually|yearly))?$/i,
      build: (m) => { const k = { double: 2, triple: 3, quadruple: 4 }[m[1].toLowerCase()]; return +m[2] > 0 ? out(`ln(${k})/ln(1 + ${m[2]}/100)`, `(1 + ${m[2]}/100)^t = ${k}, so t = ln ${k} / ln(1 + ${m[2]}/100)`, { notes: ["Years, with interest compounded once a year."] }) : null; } },
    { id: "vector-norm", re: /^(?:what is |find )?(?:the )?(?:magnitude|length|norm) of (?:the )?(?:vector )?[(<[]\s*(-?[\d.]+(?:\s*,\s*-?[\d.]+)+)\s*[)>\]]$/i,
      build: (m) => { const xs = m[1].split(/\s*,\s*/); return out(`sqrt(${xs.map((x) => `(${x})^2`).join(" + ")})`, `|v| = sqrt(${xs.map((x) => `${x}^2`).join(" + ")})`); } },
    { id: "perm-comb", re: /^(?:(?:the )?number of )?(permutations|combinations|arrangements|selections) of (\d+)(?: things| items| objects)? (?:taken|chosen|picked) (\d+)(?: at a time)?$/i,
      build: (m) => (+m[3] <= +m[2] ? out(`${/perm|arrang/i.test(m[1]) ? "nPr" : "binomial"}(${m[2]}, ${m[3]})`, `${/perm|arrang/i.test(m[1]) ? "ordered" : "unordered"} choices of ${m[3]} from ${m[2]}`) : null) },
    { id: "totient", re: /^(?:what is |find )?(?:the )?(?:euler(?:'s)? )?(?:totient|phi)(?: function)? of (\d+)$/i, build: (m) => out(`totient(${m[1]})`, `Euler's totient of ${m[1]}: how many of 1..${m[1]} are coprime to it`) },
    { id: "base-to-decimal", re: /^(?:convert )?(?:the )?(?:binary|base 2)(?: number)? ([01]+) (?:to|in|into) (?:decimal|base 10|a number)$|^(?:convert )?([01]+) (?:from binary |in binary |base 2 )(?:to|into|in) (?:decimal|base 10)$/i,
      build: (m) => out(`0b${m[1] || m[2]}`, `binary ${m[1] || m[2]} in decimal`) },
    { id: "normal-z", re: /^(?:what is )?(?:the )?probability (?:that )?z (?:is )?(less than|below|under|<|greater than|above|over|more than|>) (-?\d+(?:\.\d+)?)$/i,
      build: (m) => { const lt = /less|below|under|</i.test(m[1]); return out(lt ? `normalcdf(-oo, ${m[2]})` : `normalcdf(${m[2]}, oo)`, `standard normal: P(Z ${lt ? "<" : ">"} ${m[2]})`); } },
    { id: "normal-z", re: /^(?:what is )?(?:the )?probability (?:that )?z (?:is )?between (-?\d+(?:\.\d+)?) and (-?\d+(?:\.\d+)?)$/i,
      build: (m) => (+m[1] < +m[2] ? out(`normalcdf(${m[1]}, ${m[2]})`, `standard normal: P(${m[1]} < Z < ${m[2]})`) : null) },
    // geometry
    { id: "circle-radius", re: /^(?:what is |find )?(?:the )?(radius|diameter) of (?:a|the) circle (?:with|whose|of) (area|circumference)(?: is| of)? (\d+(?:\.\d+)?)$|^(?:a|the) circle has (?:an? )?(area|circumference) (?:of )?(\d+(?:\.\d+)?)[,.]? (?:find|what is) its (radius|diameter)$/i,
      build: (m) => { const want = (m[1] || m[6]).toLowerCase(), have = (m[2] || m[4]).toLowerCase(), v = m[3] || m[5];
        const r = have === "area" ? `sqrt(${v}/pi)` : `${v}/(2*pi)`; return out(want === "radius" ? r : `2*${r}`, `${have} ${v} gives r = ${r}${want === "diameter" ? ", d = 2r" : ""}`); } },
    { id: "square-side", re: /^(?:a|the) square has (?:an? )?(area|perimeter) (?:of )?(\d+(?:\.\d+)?)[,.]? (?:find|what is) (?:its|the) (side|side length|length of a side)$/i,
      build: (m) => out(/area/i.test(m[1]) ? `sqrt(${m[2]})` : `${m[2]}/4`, /area/i.test(m[1]) ? `side = sqrt(area ${m[2]})` : `side = perimeter ${m[2]} / 4`) },
    { id: "equilateral", re: /^(?:what is |find )?(?:the )?(area|perimeter|height) of an equilateral triangle (?:with|of) side(?: length)?(?: of)? (\d+(?:\.\d+)?)$/i,
      build: (m) => { const q = m[1].toLowerCase(), s = m[2]; return out(q === "area" ? `sqrt(3)/4*(${s})^2` : q === "perimeter" ? `3*${s}` : `sqrt(3)/2*${s}`, q === "area" ? "equilateral triangle area (sqrt 3 / 4) s^2" : q === "perimeter" ? "3 equal sides" : "height (sqrt 3 / 2) s"); } },
    { id: "semicircle", re: /^(?:what is |find )?(?:the )?area of a semi-?circle (?:with|of) (radius|diameter)(?: of)? (\d+(?:\.\d+)?)$/i,
      build: (m) => { const r = /diam/i.test(m[1]) ? `(${m[2]}/2)` : m[2]; return out(`pi*${r}^2/2`, "half of a circle's area: pi r^2 / 2"); } },
    { id: "third-angle", re: /^(?:what is |find )?(?:the )?(?:third|missing|other|remaining) angle of a triangle (?:with|whose|if the other) (?:two )?angles (?:are )?(\d+(?:\.\d+)?)(?: degrees)? and (\d+(?:\.\d+)?)(?: degrees)?$/i,
      build: (m) => (+m[1] + +m[2] < 180 ? out(`180 - ${m[1]} - ${m[2]}`, "the angles of a triangle add up to 180 degrees", { notes: ["Degrees."] }) : null) },
    { id: "complement", re: /^(?:what is |find )?(?:the )?(complement|supplement)(?:ary angle)? (?:of|to) (?:an angle of )?(\d+(?:\.\d+)?)(?: degrees?| °)?$/i,
      build: (m) => { const t = /comp/i.test(m[1]) ? 90 : 180; return +m[2] < t ? out(`${t} - ${m[2]}`, `${m[1].toLowerCase()}ary angles add up to ${t} degrees`, { notes: ["Degrees."] }) : null; } },
    { id: "polygon-sides", re: /^how many (sides|vertices|corners|edges|angles) (?:does|do) (?:a|an) ([a-z-]+) have$/i,
      build: (m) => { const n = sidesOf(m[2]); return n ? out(String(n), `a ${m[2].toLowerCase()} has ${n} ${m[1].toLowerCase()}`) : null; } },
    // statistics
    { id: "mean-first-n", re: /^(?:what is |find )?(?:the )?(?:mean|average) of the first (\d+) (?:natural|counting|positive whole) numbers$/i, build: (m) => (+m[1] >= 1 ? out(`(${m[1]} + 1)/2`, `(1 + ${m[1]})/2`) : null) },
    { id: "needed-score", re: /^what (?:score|mark|grade) do (?:i|you|we) need on the (?:next|last|\d+(?:st|nd|rd|th)) (?:test|exam|quiz) to (?:average|get an average of|have an average of) (\d+(?:\.\d+)?) if (?:i|you|we) (?:got|scored|have|had) ((?:\d+(?:\.\d+)?(?:,? (?:and )?|\s+))+\d+(?:\.\d+)?)$/i,
      build: (m) => { const xs = m[2].match(/\d+(?:\.\d+)?/g), n = xs.length + 1; return out(`${m[1]}*${n} - (${xs.join(" + ")})`, `average ${m[1]} over ${n} tests needs a total of ${m[1]} x ${n}; subtract ${xs.join(" + ")}`); } },
    // rates
    { id: "rate-time", re: /^(?:if )?(?:it takes )?(\d+(?:\.\d+)?) (hours|minutes|days) to ([a-z]+) (\d+(?:\.\d+)?) ([a-z]+),? how (?:long|many \2) (?:will it take |would it take |does it take |to [a-z]+ |for )?(?:to [a-z]+ )?(\d+(?:\.\d+)?) \5$/i,
      build: (m) => out(`${m[1]}/${m[4]}*${m[6]}`, `${m[1]} ${m[2]} for ${m[4]} ${m[5]}, so ${m[1]}/${m[4]} each; for ${m[6]}: ${m[1]}/${m[4]} x ${m[6]}`, { notes: [`In ${m[2]}; assumes a steady rate.`] }) },
    { id: "fill-time", re: /^(?:an? |the )?(?:tap|pump|hose|pipe|faucet|machine|printer|factory) (?:fills|pumps|delivers|makes|prints|produces) (\d+(?:\.\d+)?) ([a-z]+) (?:per|a|an|each) (minute|hour|second|day),? how long (?:will it take |does it take )?to (?:fill|pump|make|print|produce|deliver) (\d+(?:\.\d+)?) \2$/i,
      build: (m) => out(`${m[4]}/${m[1]}`, `${m[4]} ${m[2]} at ${m[1]} per ${m[3]}: ${m[4]} / ${m[1]}`, { notes: [`In ${m[3]}s.`] }) },
    { id: "pay-rate", re: new RegExp(String.raw`^(?:if (?:i|you|she|he|they) )?(?:earn|earning|earns|make|making|makes|get|paid|am paid|is paid|charging|charge) \$?(\d+(?:\.\d+)?)(?: dollars?| euros?| pounds?)? (?:an|per|a|each) (hour|day|week|month),? how much (?:(?:will|do|would|does) (?:i|you|she|he|they) (?:earn|make|get) )?(?:for|in|after|over) (\d+(?:\.\d+)?) \2s?$`, "i"),
      build: (m) => out(`${m[1]}*${m[3]}`, `${m[1]} per ${m[2]} x ${m[3]} ${m[2]}s`) },
    { id: "recipe-scale", re: /^(?:a|the) recipe (?:for|serves|that serves|feeding) (\d+) (?:people|servings|persons|guests)? ?(?:needs|uses|calls for|requires|takes) (\d+(?:\.\d+)?) ?([a-z]+)(?: of [a-z ]+)?,? how (?:much|many)(?: [a-z]+)? (?:is needed |do (?:i|you|we) need )?for (\d+) (?:people|servings|persons|guests)$/i,
      build: (m) => out(`${m[2]}/${m[1]}*${m[4]}`, `${m[2]} ${m[3]} for ${m[1]}, scaled to ${m[4]}: ${m[2]} x ${m[4]}/${m[1]}`, { notes: [`In ${m[3]}.`] }) },
    // number sense
    { id: "perfect-square", re: /^is (\d+) a (perfect )?(square|cube)(?: number)?$/i,
      build: (m) => { const n = +m[1], cube = /cube/i.test(m[3]), r = Math.round(cube ? Math.cbrt(n) : Math.sqrt(n)); if (n > 1e15) return null;
        const hit = (cube ? r ** 3 : r * r) === n; return hit ? out(`${n} = ${r}^${cube ? 3 : 2}`, `${n} = ${r}^${cube ? 3 : 2}, so yes`) : out(`${n} = ${r}^${cube ? 3 : 2}`, `the nearest ${cube ? "cube" : "square"} is ${r}^${cube ? 3 : 2} = ${cube ? r ** 3 : r * r}, so no`); } },
    { id: "divisible", re: /^is (\d+) divisible by (\d+)$/i, build: (m) => (+m[2] ? out(`${m[1]} mod ${m[2]} = 0`, `${m[1]} is divisible by ${m[2]} exactly when the remainder ${m[1]} mod ${m[2]} is 0`) : null) },
    { id: "next-prime", re: /^(?:what is |find )?(?:the )?(?:smallest|first|next) prime (?:number )?(?:greater than|bigger than|larger than|after|above|over) (\d+)$/i,
      build: (m) => { let n = +m[1] + 1; if (n > 1e9) return null; while (!isPrimeN(n)) n++; return out(`${n}`, `${n} is the first prime after ${m[1]} (${Array.from({ length: n - +m[1] - 1 }, (_, i) => +m[1] + 1 + i).join(", ") || "none"} ${n - +m[1] - 1 ? "are composite" : "in between"})`, { notes: ["Checked by trial division."] }); } },
    { id: "digit-sum", re: /^(?:what is |find )?(?:the )?sum of (?:the |its )?digits (?:of|in) (\d+)$/i, build: (m) => out(m[1].split("").join(" + "), `digits of ${m[1]}: ${m[1].split("").join(" + ")}`) },
    { id: "digit-count", re: /^how many digits (?:are )?(?:there )?(?:in|does) (\d+) ?\^ ?(\d+)(?: have)?$/i,
      build: (m) => { const a = BigInt(m[1]), b = +m[2]; if (b > 20000 || a < 1n) return null; const d = (a ** BigInt(b)).toString().length; return out(String(d), `${m[1]}^${m[2]} has ${d} digits (computed exactly)`); } },
    { id: "roman", re: /^(?:what is |convert )?(?:the )?(?:roman numeral )?([mdclxvi]+)(?: in roman numerals?| roman numerals?)?(?: (?:to|in|as) (?:a )?(?:numbers?|decimal|arabic numerals?))?$/i,
      build: (m) => { if (!/roman/i.test(m[0]) && !/(?:to|in|as) (?:a )?(?:numbers?|decimal|arabic)/i.test(m[0])) return null; const s = m[1].toLowerCase();
        if (!/^m{0,4}(cm|cd|d?c{0,3})(xc|xl|l?x{0,3})(ix|iv|v?i{0,3})$/.test(s)) return null;
        const parts = []; for (let i = 0; i < s.length; i++) { const v = ROMAN[s[i]], nx = ROMAN[s[i + 1]] || 0; if (v < nx) { parts.push(`(${nx} - ${v})`); i++; } else parts.push(String(v)); }
        return out(parts.join(" + "), `${m[1].toUpperCase()} = ${parts.join(" + ")}`); } },
    // "what is 3 less than 20" is 17 ("is 3 less than 20" stays a comparison)
    { id: "more-less-than", re: /^(?:what is|what number is|find|calculate|compute|work out) (.+?) (more|less|fewer) than (.+)$/i,
      build: (m) => { if (/%|percent/i.test(m[1] + m[3])) return null; const a = E(m[1]), b = E(m[3]);
        if (!a || !b || /[a-z=<>]/i.test(a.replace(/sqrt|pi/g, "") + b.replace(/sqrt|pi/g, ""))) return null;
        const up = /more/i.test(m[2]); return out(`(${b}) ${up ? "+" : "-"} (${a})`, `${a} ${up ? "more" : "less"} than ${b}: ${b} ${up ? "+" : "-"} ${a}`); } },
    { id: "square-cube-of", re: /^(?:what is |find |calculate )?(?:the )?(square|cube) of (-?\d+(?:\.\d+)?(?:\/\d+)?)$/i,
      build: (m) => out(`(${m[2]})^${/cube/i.test(m[1]) ? 3 : 2}`, `the ${m[1].toLowerCase()} of ${m[2]}`) },
    { id: "percent-of-percent", re: /^(?:what is |find |calculate )?((?:\d+(?:\.\d+)? ?(?:%|percent|per cent) of ){2,})(\d+(?:\.\d+)?)$/i,
      build: (m) => { const ps = m[1].match(/\d+(?:\.\d+)?/g); return out(`${ps.map((p) => `${p}/100`).join(" * ")} * ${m[2]}`, ps.map((p) => `${p}%`).join(" of ") + ` of ${m[2]}`); } },
    // sums of whole-number ranges: "sum of 1 through 100", "add all numbers from 1 to 50"
    { id: "sum-range", re: /^(?:what is |find |calculate |compute )?(?:the )?(?:sum|total) of (?:all )?(?:the )?(?:(?:whole |natural |counting |positive )?(?:numbers|integers) )?(?:from )?(-?\d+) (?:to|through|thru|until|up to) (-?\d+)(?: inclusive)?$/i,
      build: (m) => (+m[1] <= +m[2] ? out(`sum(k, k, ${m[1]}, ${m[2]})`, `${m[1]} + ${+m[1] + 1} + ... + ${m[2]}`) : null) },
    { id: "sum-range", re: /^add (?:up )?(?:all )?(?:the )?(?:(?:whole |natural |counting |positive )?(?:numbers|integers) )?from (-?\d+) (?:to|through|thru|up to) (-?\d+)(?: inclusive)?$/i,
      build: (m) => (+m[1] <= +m[2] ? out(`sum(k, k, ${m[1]}, ${m[2]})`, `${m[1]} + ${+m[1] + 1} + ... + ${m[2]}`) : null) },
    { id: "sum-first-n", re: /^(?:what is |find |calculate )?(?:the )?sum of (?:the )?first (\d+) (odd|even|natural|counting|positive)? ?(?:whole )?(?:numbers|integers)$/i,
      build: (m) => { const k = (m[2] || "natural").toLowerCase(), term = k === "odd" ? "2k - 1" : k === "even" ? "2k" : "k";
        return +m[1] <= 1e6 ? out(`sum(${term}, k, 1, ${m[1]})`, `the first ${m[1]} ${k === "odd" || k === "even" ? k : "positive whole"} numbers: sum of ${term} for k = 1..${m[1]}`) : null; } },
    { id: "goes-into", re: /^how many times (?:does|will|can|would) (\d+(?:\.\d+)?) (?:go|fit) into (\d+(?:\.\d+)?)$/i,
      build: (m) => out(`${m[2]}/${m[1]}`, `${m[2]} / ${m[1]}`) },
    // money
    { id: "tip-on", re: new RegExp(String.raw`^(?:what is |how much is |calculate |find )?(?:an? |the )?(\d+(?:\.\d+)?) ?(?:%|percent|per cent) tip (?:on|for) (?:an? |the |my )?${AMT}(?: (?:bill|meal|check|tab|dinner|order))?$`, "i"),
      build: (m) => out(`${m[1]}/100*${m[2]}`, `tip = ${m[1]}% of ${m[2]}`) },
    { id: "split-among", re: new RegExp(String.raw`^(?:split|divide|share) ${AMT} (?:equally |evenly )?(?:among|between|amongst|by|with|into) (\d+)(?: (?:people|persons|friends|ways|kids|children|of us|workers|parts|groups))?$`, "i"),
      build: (m) => out(`${m[1]}/${m[2]}`, `${m[1]} shared equally by ${m[2]}: ${m[1]} / ${m[2]}`) },
    { id: "sale-price", re: new RegExp(String.raw`^(?:an? |the )?(?:\w+ )?(?:costs?|is priced at|priced at|is) ${AMT} and is (\d+(?:\.\d+)?) ?(?:%|percent) off,? (?:what is|what's|find|how much is) the (?:sale|new|final|discounted|reduced) price$`, "i"),
      build: (m) => out(`${m[1]}*(1 - ${m[2]}/100)`, `${m[1]} less ${m[2]}%: ${m[1]} x (1 - ${m[2]}/100)`) },
    { id: "original-price", re: new RegExp(String.raw`^(?:i |we |you |she |he |they )?(?:paid|pay|spent) ${AMT} (?:after|with) an? (\d+(?:\.\d+)?) ?(?:%|percent) (?:discount|reduction|markdown|off),? (?:what was|what is|find) the (?:original|regular|full|old) price$`, "i"),
      build: (m) => (+m[2] < 100 ? out(`${m[1]}/(1 - ${m[2]}/100)`, `the paid price is (100 - ${m[2]})% of the original: ${m[1]} / (1 - ${m[2]}/100)`) : null) },
    { id: "compound-amount", re: new RegExp(String.raw`^how much (?:is|will) ${AMT} (?:be )?(?:worth )?(?:after|in) (\d+(?:\.\d+)?) years? at (\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:interest|per year|a year|annually|per annum))?,? compounded (annually|yearly)$`, "i"),
      build: (m) => out(`${m[1]}*(1 + ${m[3]}/100)^${m[2]}`, `A = P (1 + r)^t with P = ${m[1]}, r = ${m[3]}%, t = ${m[2]}`) },
    // "if i save 25 dollars a week how much in a year": only the fixed-length periods
    { id: "save-per", re: new RegExp(String.raw`^(?:if )?(?:i |you |we |she |he |they )?(?:save|saves|earn|earns|make|makes|put away|puts away|spend|spends) ${AMT} (?:a|per|each|every) (day|week|hour),? how much (?:(?:will|do|would|does) (?:i|you|we|she|he|they) (?:have|save|earn|make|spend) |is that |in total )?(?:in|after|over) (?:a|one|1|(\d+)) (week|year|day)s?$`, "i"),
      build: (m) => { const per = { "day-week": 7, "day-year": 365, "week-year": 52, "hour-day": 24, "hour-week": 168 }[`${m[2].toLowerCase()}-${m[4].toLowerCase()}`];
        if (!per) return null; const k = m[3] || 1; return out(`${m[1]}*${per}*${k}`, `${m[1]} each ${m[2]}, ${per} ${m[2]}s in a ${m[4]}${k != 1 ? `, for ${k} ${m[4]}s` : ""}`, { notes: m[4] === "year" && m[2] === "week" ? ["Uses 52 weeks in a year."] : m[4] === "year" ? ["Uses 365 days in a year."] : [] }); } },
    { id: "profit", re: new RegExp(String.raw`^(?:what is |find |calculate )?(?:the )?(profit|loss|gain)( percent(?:age)?| %)? (?:if|when) (?:it is |it was |an item is |an item was |something is )?(?:bought|purchased) (?:for|at) ${AMT} and sold (?:for|at) ${AMT}$`, "i"),
      build: (m) => profitOf(m[1], !!m[2], m[3], m[4]) },
    { id: "profit", re: new RegExp(String.raw`^(?:what is |find |calculate )?(?:the )?(profit|loss|gain)( percent(?:age)?| %)? (?:if|when) (?:the )?cost price is ${AMT},? and (?:the )?sell(?:ing)? price is ${AMT}$`, "i"),
      build: (m) => profitOf(m[1], !!m[2], m[3], m[4]) },
    // "3 apples cost 1.50, how much do 7 apples cost" / "if a dozen eggs cost 3 dollars how much is one egg"
    { id: "unit-price", re: new RegExp(String.raw`^(?:if )?(a dozen|dozen|a pair of|a|an|one|two|three|four|five|six|seven|eight|nine|ten|\d+) ([a-z]+) costs? ${AMT},? (?:then )?how much (?:is|are|does|do|would|will) (a dozen|a pair of|a|an|one|two|three|four|five|six|seven|eight|nine|ten|\d+) ([a-z]+)(?: cost)?$`, "i"),
      build: (m) => { const a = WN(m[1]), b = WN(m[4]); if (!a || !b || stem(m[2]) !== stem(m[5])) return null;
        return out(`${m[3]}/${a}*${b}`, `${a} cost ${m[3]}, so one costs ${m[3]}/${a}; ${b} cost ${m[3]}/${a} x ${b}`); } },
    // work shared by more hands: "if 5 workers take 8 days, how many days for 10 workers"
    { id: "workers", re: /^(?:if )?(\d+) (workers|people|men|women|machines|painters|builders|pumps|robots|cooks|farmers)(?: can)? (?:take|need|finish (?:a |the )?(?:job|work|task|wall|house) in|do (?:a |the )?(?:job|work) in|complete (?:a |the )?(?:job|work|task) in|build (?:a |the )?(?:wall|house) in|paint (?:a |the )?(?:house|wall|fence) in) (\d+(?:\.\d+)?) (days|hours|minutes|weeks),? how (?:many (days|hours|minutes|weeks)|long) (?:will |would |does |do )?(?:it take )?(?:for )?(\d+) \2(?: take| need)?$/i,
      build: (m) => { if (m[5] && m[5].toLowerCase() !== m[4].toLowerCase()) return null;
        return out(`${m[1]}*${m[3]}/${m[6]}`, `the job is ${m[1]} x ${m[3]} ${m[2]}-${m[4]}; shared by ${m[6]}: ${m[1]} x ${m[3]} / ${m[6]}`, { notes: ["Assumes everyone works at the same steady rate."] }); } },
    // "i have 3 boxes with 12 eggs each, how many eggs"
    { id: "groups-each", re: /^(?:i have |we have |there are |you have |she has |he has |they have )?(\d+) ([a-z]+) (?:with|of|containing|holding|that hold|that each hold|each with|each holding|each containing) (\d+) ([a-z]+)(?: each| in each| apiece)?,? how many ([a-z]+)(?: are there| in total| altogether| total| do (?:i|we|you|they) have| are in all)?$/i,
      build: (m) => { if (!/\beach\b|apiece/i.test(m[0]) || stem(m[4]) !== stem(m[5])) return null; return out(`${m[1]}*${m[3]}`, `${m[1]} ${m[2]} x ${m[3]} ${m[4]} each`); } },
    // "there are 24 students and a third are boys, how many boys"
    { id: "fraction-of-group", re: /^(?:there are |a class has |a group has |the class has |we have )?(\d+) ([a-z]+)(?: in (?:a|the) (?:class|group|room|school|team))? and (half|a half|one half|a third|one third|two thirds|a quarter|one quarter|three quarters|a fourth|a fifth|two fifths|three fifths|a tenth|(\d+(?:\.\d+)?) ?(?:%|percent)) (?:of them )?are ([a-z]+),? how many (?:are )?([a-z]+)(?: are there)?$/i,
      build: (m) => { if (stem(m[5]) !== stem(m[6])) return null; const f = m[4] ? [+m[4], 100] : FRACTION_WORD[m[3].toLowerCase()]; if (!f) return null;
        const v = +m[1] * f[0] / f[1]; if (!Number.isInteger(v)) return null; // a count of people has to be whole
        return out(`${m[1]}*${f[0]}/${f[1]}`, `${m[3]} of ${m[1]}: ${m[1]} x ${f[0]}/${f[1]}`); } },
    // "a pizza has 8 slices, 3 people eat 2 each, how many slices are left"
    { id: "left-after-each", re: /^(?:a|an|the) ([a-z]+) (?:has|had|is cut into) (\d+) ([a-z]+),? (?:and )?(\d+) (?:people|friends|kids|children|of us|students|boys|girls) (?:each )?(?:eat|ate|take|took|get|got|have|had|use|used) (\d+)(?: \3)?(?: each)?,? how many (?:\3 )?(?:are|is) left(?: over)?$/i,
      build: (m) => { if (!/\beach\b/i.test(m[0])) return null; const v = +m[2] - +m[4] * +m[5]; if (v < 0) return null;
        return out(`${m[2]} - ${m[4]}*${m[5]}`, `${m[2]} ${m[3]} minus ${m[4]} x ${m[5]} eaten`); } },
    // "ratio 3:5, total 40, what is the larger part"
    { id: "ratio-part", re: /^(?:the )?ratio (?:is )?(\d+) ?: ?(\d+),? (?:and )?(?:the )?(?:total|sum)(?: is)? (\d+(?:\.\d+)?),? (?:what is|find) the (larger|smaller|bigger|greater|first|second) (?:part|share|number|amount)$/i,
      build: (m) => { const a = +m[1], b = +m[2], k = m[4].toLowerCase(); if (a === b && !/first|second/.test(k)) return null;
        const pick = k === "first" ? a : k === "second" ? b : /larger|bigger|greater/.test(k) ? Math.max(a, b) : Math.min(a, b);
        return out(`${m[3]}*${pick}/(${a} + ${b})`, `${m[3]} split ${a}:${b}; the ${k} part is ${m[3]} x ${pick}/${a + b}`); } },
    // "if 3x = 21 what is x"
    { id: "solve-leading", re: /^(?:if|given|given that|suppose|when) (.+?=.+?),? (?:then )?(?:what is|what's|find|solve for|what does) ([a-z])(?: equal)?$/i,
      build: (m) => { const t = E(m[1]); if (!t || (t.match(/=/g) || []).length !== 1 || !new RegExp(`(?<![A-Za-z_])${m[2]}(?![A-Za-z_(])`).test(t)) return null;
        return { math: t, goal: "solve", variable: m[2], interpretation: `solve ${t} for ${m[2]}` }; } },
    // "solve x^2 = 49 for positive x"
    { id: "solve-sign", re: /^(?:solve )?(.+?=.+?) for (?:the )?(positive|negative) (?:value of )?([a-z])$/i,
      build: (m) => { const t = E(m[1]); if (!t || (t.match(/=/g) || []).length !== 1) return null;
        return { math: `${t}, ${m[3]} ${/pos/i.test(m[2]) ? ">" : "<"} 0`, goal: "solve", variable: m[3], interpretation: `solve ${t} with ${m[3]} ${/pos/i.test(m[2]) ? "> 0" : "< 0"}` }; } },
    // "inequality 2x - 5 > 3" with no verb: the relation itself is the request
    { id: "inequality", re: /^(?:the )?(?:inequality|inequalities)[:\s]+(.+)$/i,
      build: (m) => { const t = E(m[1]); return t && /[<>]/.test(t) && !/=$/.test(t) ? { math: t, goal: "solve", interpretation: `solve the inequality ${t}` } : null; } },
    // "two numbers add to 20 and differ by 4" / "find two numbers whose sum is 20 and whose product is 96"
    { id: "sum-difference", re: /^(?:find )?(?:two (?:numbers|integers)|2 numbers) (?:that |which |whose )?(?:add (?:up )?to|sum to|sum is|with (?:a )?sum(?: of)?|have (?:a )?sum(?: of)?|total(?:ing)?) (\S+?)(?:,| and|, and)? (?:that |which |whose |their |with |have |having |a |and )*(difference(?: is| of)?|differ by|product(?: is| of)?|multiply to) (\S+)$/i,
      build: (m) => { const p = two(m[1].replace(/[,.]$/, ""), m[3].replace(/[,.]$/, "")); if (!p) return null; const prod = /product|multiply/i.test(m[2]);
        return { math: prod ? `x + y = ${p[0]}, x*y = ${p[1]}` : `x + y = ${p[0]}, x - y = ${p[1]}`, goal: "solve", interpretation: prod ? `let the numbers be x and y: x + y = ${p[0]}, xy = ${p[1]}` : `let the numbers be x >= y: x + y = ${p[0]}, x - y = ${p[1]}` }; } },
    // "is 2^31 - 1 prime": a whole-number expression, computed exactly first
    { id: "is-prime", re: /^is (.+?) (?:a )?prime(?: number)?(?: or (?:composite|not))?$/i,
      build: (m) => { const x = E(m[1]); if (!x || !/^[\d\s^+\-*()]+$/.test(x) || !/[\^+\-*]/.test(x)) return null;
        const big = (x.match(/\^\s*\(?(\d+)/g) || []).some((p) => +p.replace(/^\^\s*\(?/, "") > 400); // keep the exact value small enough to test and prove quickly
        return big ? null : out(`isprime(${x})`, `is ${x} prime`, { goal: "evaluate" }); } },
    // number bases with a stated source base: "1010 base 2 to base 8", "0xff in binary", "ff hex to octal"
    { id: "base-to-base", re: /^(?:convert |write |express |what is )?(?:the )?(?:number )?(0x[0-9a-f]+|0b[01]+|0o[0-7]+|[0-9a-z]+(?:_\d+| (?:from |in )?(?:binary|octal|hexadecimal|hex|ternary|base[- ]?\d+))) (?:to|in|into|as) (binary|octal|hexadecimal|hex|ternary|base[- ]?\d+|decimal|base[- ]?10|denary)$/i,
      build: (m) => {
        const src = m[1].toLowerCase(); let digits, b1;
        const lit = /^0([xbo])([0-9a-f]+)$/.exec(src);
        if (lit) { b1 = { x: 16, b: 2, o: 8 }[lit[1]]; digits = lit[2]; }
        else { const q = /^([0-9a-z]+)(?:_(\d+)| (?:from |in )?(.+))$/.exec(src); if (!q) return null; digits = q[1]; b1 = q[2] ? Number(q[2]) : baseOf(q[3]); }
        const b2 = /^(?:decimal|denary|base[- ]?10)$/i.test(m[2]) ? 10 : baseOf(m[2]);
        if (!b1 || !b2 || b1 < 2 || b1 > 36 || b2 < 2 || b2 > 36 || b1 === b2 || digits.length > 200) return null;
        const vals = [...digits].map((c) => parseInt(c, 36)); if (vals.some((v) => !(v < b1))) return null;
        let v = 0n; for (const d of vals) v = v * BigInt(b1) + BigInt(d);
        if (b2 === 10) return out(vals.map((d, i) => `${d}*${b1}^${vals.length - 1 - i}`).join(" + "), `positional value of ${digits} in base ${b1}`);
        return out(`tobase(${v}, ${b2})`, `${digits} in base ${b1} is ${v} in decimal; written in base ${b2}`);
      } },
    // repeated dice: "probability of rolling a 6 twice in a row", "chance of two sixes with two dice"
    { id: "prob-die-repeat", re: /^(?:what (?:is|are) )?(?:the )?(probability|chance|odds) (?:of )?(?:rolling|getting|throwing) (?:a |an )?(?:[1-6]|one|two|three|four|five|six) (twice|three times|four times|five times|(\d+) times)(?: in a row)?(?: (?:on|with|using) (?:a |one |the )?(?:fair |single |standard |six[- ]sided |regular )*(?:die|dice))?$/i,
      build: (m) => { const k = m[3] ? +m[3] : { twice: 2, "three times": 3, "four times": 4, "five times": 5 }[m[2].toLowerCase()]; if (!(k >= 2 && k <= 60)) return null;
        return out(`(1/6)^${k}`, `${k} independent rolls of a fair die, each 1/6: (1/6)^${k}`, { notes: /odds/i.test(m[1]) ? [`Read "odds" as a probability; as odds against it is ${6 ** k - 1} : 1.`] : [] }); } },
    { id: "prob-die-repeat", re: /^(?:what (?:is|are) )?(?:the )?(probability|chance|odds) (?:of )?(?:rolling |getting |throwing )?(?:(two|three|four|five|\d+) (?:sixes|fives|fours|threes|twos|ones|[1-6](?:s|'s))|(double (?:six|sixes|[1-6])|snake eyes))(?: in a row)?(?: (?:on|with|using) (two|three|four|five|\d+) (?:fair |standard |six[- ]sided |regular )*dice)?$/i,
      build: (m) => { const W = { two: 2, three: 3, four: 4, five: 5 }; const k = m[3] ? 2 : W[m[2].toLowerCase()] || +m[2]; const n = m[4] ? W[m[4].toLowerCase()] || +m[4] : k;
        if (!(k >= 2 && k <= 60) || n !== k) return null;
        return out(`(1/6)^${k}`, `${k} dice each showing the named face, 1/6 each: (1/6)^${k}`, { notes: /odds/i.test(m[1]) ? [`Read "odds" as a probability; as odds against it is ${6 ** k - 1} : 1.`] : [] }); } },
    { id: "vector-angle", re: /^(?:what is |find |calculate |compute )?(?:the )?angle between (?:the )?(?:vectors? )?[(<[]\s*(-?[\d.]+(?:\s*,\s*-?[\d.]+)+)\s*[)>\]] and (?:the )?(?:vector )?[(<[]\s*(-?[\d.]+(?:\s*,\s*-?[\d.]+)+)\s*[)>\]](?: (in degrees)| in radians)?$/i,
      build: (m) => vectorAngle(m[1], m[2], !!m[3], out) },
    { id: "mixed-units", re: /^(?:convert |what is |express |write )?(\d+(?:\.\d+)?) ([a-z]+)(?:,| and|, and)? (\d+(?:\.\d+)?) ([a-z]+) (?:to|in|into|as) (?:total |just |only )?([a-z]+)$/i,
      build: (m) => mixedUnits(m[1], m[2], m[3], m[4], m[5], out) },
    { id: "mixed-units", re: /^how many ([a-z]+) (?:is|are|in|make|equal) (\d+(?:\.\d+)?) ([a-z]+)(?:,| and|, and)? (\d+(?:\.\d+)?) ([a-z]+)$/i,
      build: (m) => mixedUnits(m[2], m[3], m[4], m[5], m[1], out) },
    // "a shirt costs 40 after a 20% discount, what was the original price"
    { id: "original-price", re: new RegExp(String.raw`^(?:an? |the )?(?:[a-z]+ )?(?:costs?|is|was|sells? for|now costs|is now|is priced at|is selling for|sold for) ${AMT} after an? (\d+(?:\.\d+)?) ?(?:%|percent) (?:discount|reduction|markdown|off|price cut)[,.]? (?:what was|what is|what's|find) (?:the |its )?(?:original|regular|full|old|list|pre-sale) price$`, "i"),
      build: (m) => (+m[2] < 100 ? out(`${m[1]}/(1 - ${m[2]}/100)`, `the sale price is (100 - ${m[2]})% of the original: ${m[1]} / (1 - ${m[2]}/100)`) : null) },
    // ---- round 7: quantities, counting, sectors, finance ----
    { id: "dozen", re: /^(?:what is |how much is |how many is |how many are )?(half a|a|an|one|two|three|four|five|six|seven|eight|nine|ten|\d+(?:\.\d+)?) dozen(?: [a-z]+)?$/i,
      build: (m) => { const k = /^half a$/i.test(m[1]) ? "1/2" : WN(m[1]); return k ? out(`${k}*12`, `${m[1].toLowerCase()} dozen: ${k} x 12`) : null; } },
    { id: "choose-k", re: /^how many ways (?:are there )?(?:can (?:i|you|we|one|she|he) |to |of )?(?:choose|choosing|pick|picking|select|selecting|form|forming) (?:a |an )?(?:committee|team|group|subset|sample|set|hand)? ?(?:of )?(\d+) (?:people |members |students |items |objects |things |players |cards |books |letters )?(?:from|out of|of|among) (?:a (?:group|class|team|set|deck|pool) of )?(\d+)(?: [a-z]+)?$/i,
      build: (m) => (+m[1] <= +m[2] ? out(`binomial(${m[2]}, ${m[1]})`, `unordered choice of ${m[1]} from ${m[2]}: C(${m[2]}, ${m[1]})`) : null) },
    { id: "arrange-k", re: /^how many ways (?:are there )?(?:can (?:i|you|we|one) |to |of )?(?:arrange|arranging|order|ordering|line up|lining up|rank|ranking|seat|seating) (\d+) (?:of |from |out of )(?:the |a group of )?(\d+)(?: [a-z]+)?(?: in a (?:row|line))?$/i,
      build: (m) => (+m[1] <= +m[2] ? out(`nPr(${m[2]}, ${m[1]})`, `ordered choice of ${m[1]} from ${m[2]}: P(${m[2]}, ${m[1]})`) : null) },
    { id: "outcomes", re: /^how many (?:possible |different |total )?(?:outcomes|results)(?: are there| are possible)? (?:when|if|from|for|of) (?:you |i |we )?(?:flip(?:ping)?|toss(?:ing)?|roll(?:ing)?|throw(?:ing)?) (\d+|two|three|four|five|six|seven|eight|nine|ten|a|one) (?:fair )?(coins?|dice|die)$/i,
      build: (m) => { const n = WN(m[1]); if (!n || n > 60) return null; const die = /di/i.test(m[2]); return out(`${die ? 6 : 2}^${n}`, `${n} ${die ? "dice with 6 faces" : "coins with 2 sides"} each: ${die ? 6 : 2}^${n} equally likely outcomes`); } },
    { id: "count-multiples", re: /^how many (?:(?:whole |positive |natural )?(?:numbers|integers) )?(?:that are )?(?:multiples of|divisible by) (\d+) (?:are there |are |lie |exist )?(?:between (\d+) and (\d+)|(?:up to|at most|not exceeding|from 1 to|less than or equal to) (\d+)|(?:below|under|less than|smaller than) (\d+))(?: inclusive)?$/i,
      build: (m) => { const k = +m[1]; if (!k) return null;
        if (m[2]) return out(`floor(${m[3]}/${k}) - floor((${m[2]} - 1)/${k})`, `multiples of ${k} from ${m[2]} to ${m[3]}: floor(${m[3]}/${k}) - floor((${m[2]} - 1)/${k})`, { notes: [`Counting ${m[2]} and ${m[3]} themselves when they are multiples of ${k}.`] });
        if (m[4]) return out(`floor(${m[4]}/${k})`, `multiples of ${k} from 1 to ${m[4]}: floor(${m[4]}/${k})`);
        return out(`floor((${m[5]} - 1)/${k})`, `positive multiples of ${k} below ${m[5]}: floor((${m[5]} - 1)/${k})`); } },
    { id: "count-parity", re: /^how many (even|odd) (?:numbers|integers|whole numbers) (?:are there )?(?:between (\d+) and (\d+)|(?:up to|from 1 to|at most) (\d+)|(?:below|under|less than) (\d+))(?: inclusive)?$/i,
      build: (m) => { const even = /even/i.test(m[1]); const cnt = (a, b) => even ? `floor(${b}/2) - floor((${a} - 1)/2)` : `floor((${b} + 1)/2) - floor(${a}/2)`;
        if (m[2]) return +m[2] <= +m[3] ? out(cnt(m[2], m[3]), `${m[1].toLowerCase()} numbers from ${m[2]} to ${m[3]}`, { notes: [`Counting ${m[2]} and ${m[3]} themselves when they are ${m[1].toLowerCase()}.`] }) : null;
        if (m[4]) return out(cnt(1, m[4]), `${m[1].toLowerCase()} numbers from 1 to ${m[4]}`);
        return out(cnt(1, +m[5] - 1), `${m[1].toLowerCase()} numbers from 1 to ${+m[5] - 1}`); } },
    { id: "count-primes", re: /^how many primes? (?:numbers )?(?:are there |are |exist )?(?:(?:below|under|less than|smaller than) (\d+)|(?:up to|at most|not exceeding|less than or equal to|from 1 to|from 2 to) (\d+)|between (\d+) and (\d+))(?: inclusive)?$/i,
      build: (m) => { const lim = (v) => +v <= 20000000;
        if (m[1]) return lim(m[1]) ? out(`primepi(${+m[1] - 1})`, `primes up to ${+m[1] - 1}: pi(${+m[1] - 1})`) : null;
        if (m[2]) return lim(m[2]) ? out(`primepi(${m[2]})`, `primes up to ${m[2]}: pi(${m[2]})`) : null;
        return lim(m[4]) && +m[3] <= +m[4] ? out(`primepi(${m[4]}) - primepi(${+m[3] - 1})`, `primes from ${m[3]} to ${m[4]}: pi(${m[4]}) - pi(${+m[3] - 1})`, { notes: [`Counting ${m[3]} and ${m[4]} themselves when prime.`] }) : null; } },
    { id: "nth-parity", re: /^(?:what is |find )?(?:the )?(\d+)(?:st|nd|rd|th) (odd|even) (?:number|integer|whole number)$/i,
      build: (m) => (+m[1] >= 1 ? out(/odd/i.test(m[2]) ? `2*${m[1]} - 1` : `2*${m[1]}`, `the ${m[1]}th ${m[2].toLowerCase()} number: ${/odd/i.test(m[2]) ? "2n - 1" : "2n"} with n = ${m[1]}`) : null) },
    { id: "part-of-unit", re: /^what (fraction|percent|percentage|part|proportion) of (?:a|an|one) ([a-z]+) is (\d+(?:\.\d+)?) ([a-z]+)$|^(\d+(?:\.\d+)?) ([a-z]+) is what (fraction|percent|percentage|part|proportion) of (?:a|an|one) ([a-z]+)$/i,
      build: (m) => { const [kind, big, n, small] = m[1] ? [m[1], m[2], m[3], m[4]] : [m[7], m[8], m[5], m[6]]; const a = mixedUnit(big), b = mixedUnit(small);
        if (!a || !b || a[0] !== b[0] || a[1] <= b[1]) return null; const pct = /percent/i.test(kind);
        return out(pct ? `${n}*${b[1]}/${a[1]}*100` : `${n}*${b[1]}/${a[1]}`, `one ${big} is ${a[1] / b[1]} ${small}: ${n}/${a[1] / b[1]}${pct ? " x 100" : ""}`, { notes: pct ? ["The answer is in percent."] : [] }); } },
    // circle parts: sector arc length and area, semicircle perimeter, rhombus / kite from diagonals, parallelogram without "with"
    { id: "sector", re: /^(?:what is |find |calculate )?(?:the )?(arc length|area|perimeter) of (?:a |the )?(?:circular )?(?:(\d+(?:\.\d+)?) ?(?:degrees?|°) )?sector (?:of a circle )?(?:with|of|whose|having) (?:a )?radius(?: of| is| =)? ?(\d+(?:\.\d+)?)(?: (?:and|with) (?:a )?(?:central |sector )?angle(?: of| is| =)? ?(\d+(?:\.\d+)?|pi\/\d+|\d*pi(?:\/\d+)?) ?(degrees?|°|radians?|rad)?)?$/i,
      build: (m) => { const q = m[1].toLowerCase(), r = m[3]; let th = m[2] || m[4]; if (!th) return null; const rad = /rad/i.test(m[5] || "") || /pi/.test(th); if (!rad && +th > 360) return null;
        const frac = rad ? `(${th})/(2*pi)` : `${th}/360`; const arc = `${frac}*2*pi*${r}`, area = `${frac}*pi*${r}^2`;
        return out(q === "area" ? area : q === "arc length" ? arc : `${arc} + 2*${r}`, `${q} of a sector: ${q === "area" ? "(angle/full turn) x pi r^2" : q === "arc length" ? "(angle/full turn) x 2 pi r" : "arc + two radii"} with r = ${r}, angle ${th}${rad ? " rad" : " degrees"}`); } },
    { id: "semicircle-perimeter", re: /^(?:what is |find |calculate )?(?:the )?perimeter of a semi-?circle (?:with|of|whose) (radius|diameter)(?: of| is| =)? ?(\d+(?:\.\d+)?)$/i,
      build: (m) => { const r = /diam/i.test(m[1]) ? `(${m[2]}/2)` : m[2]; return out(`pi*${r} + 2*${r}`, "half the circumference plus the diameter: pi r + 2r"); } },
    { id: "rhombus", re: /^(?:what is |find |calculate )?(?:the )?area of a (rhombus|kite) (?:with|whose|of) diagonals(?: of)? (\d+(?:\.\d+)?) and (\d+(?:\.\d+)?)$/i,
      build: (m) => out(`${m[2]}*${m[3]}/2`, `${m[1].toLowerCase()} area: half the product of the diagonals, d1 d2 / 2`) },
    { id: "parallelogram", re: /^(?:what is |find |calculate )?(?:the )?area of a parallelogram (?:with |of |whose )?base(?: of| is| =)? ?(\d+(?:\.\d+)?)(?:,? and| with|,)? (?:a )?height(?: of| is| =)? ?(\d+(?:\.\d+)?)$/i,
      build: (m) => out(`${m[1]}*${m[2]}`, "parallelogram area base x height") },
    // finance with a compounding frequency; money answers are shown to the cent
    { id: "compound-freq", re: new RegExp(String.raw`^(?:what is |find |calculate )?(?:the )?(compound interest|interest earned|interest|amount|future value|final amount|final value|value|balance) (?:on|of|for) (?:an? (?:investment|deposit|loan) of )?${AMT} (?:invested |deposited |borrowed )?at (\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:per year|a year|annual(?:ly)?|interest|per annum|apr))* (?:for|over|after) (\d+(?:\.\d+)?) years?,? compounded (annually|yearly|semi-?annually|quarterly|monthly|weekly|daily)$`, "i"),
      build: (m) => { const f = { annually: 1, yearly: 1, semiannually: 2, "semi-annually": 2, quarterly: 4, monthly: 12, weekly: 52, daily: 365 }[m[5].toLowerCase()]; const A = f === 1 ? `${m[2]}*(1 + ${m[3]}/100)^${m[4]}` : `${m[2]}*(1 + ${m[3]}/(100*${f}))^(${f}*${m[4]})`;
        const interest = /interest/i.test(m[1]); return out(interest ? `${A} - ${m[2]}` : A, `A = P (1 + r/n)^(n t) with P = ${m[2]}, r = ${m[3]}%, n = ${f}, t = ${m[4]}${interest ? "; interest = A - P" : ""}`, { places: 2, notes: ["Rounded to the cent in the decimal value."] }); } },
    { id: "loan-payment", re: new RegExp(String.raw`^(?:what is |find |calculate )?(?:the )?monthly (?:payment|repayment|instal?lment) (?:on|for|of) (?:a |an )?${AMT} (?:loan |mortgage |car loan |home loan )?(?:at |with |with an? (?:interest |apr )?(?:rate )?of )(\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:interest|apr|annual interest|per year|a year|annual))* (?:for|over) (\d+) (years?|months?)$`, "i"),
      build: (m) => { const n = /month/i.test(m[4]) ? m[3] : `${m[3]}*12`; return +m[2] > 0 ? out(`${m[1]}*(${m[2]}/1200)/(1 - (1 + ${m[2]}/1200)^(-(${n})))`, `amortised loan: payment = P r / (1 - (1 + r)^-n) with P = ${m[1]}, monthly rate r = ${m[2]}%/12, n = ${n} months`, { places: 2, notes: ["Fixed monthly payments with interest compounded monthly; rounded to the cent in the decimal value."] }) : null; } },
    { id: "annuity-fv", re: new RegExp(String.raw`^(?:what is |find |calculate )?(?:the )?future value of (?:saving |investing |depositing |paying |putting away )?${AMT} (?:a|per|each|every) month (?:at|earning|with) (\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:per year|a year|annual(?:ly)?|interest|per annum))* (?:for|over) (\d+) years?$`, "i"),
      build: (m) => out(`${m[1]}*((1 + ${m[2]}/1200)^(12*${m[3]}) - 1)/(${m[2]}/1200)`, `ordinary annuity: FV = PMT ((1 + r)^n - 1)/r with PMT = ${m[1]}, monthly r = ${m[2]}%/12, n = 12 x ${m[3]}`, { places: 2, notes: ["Deposits at the end of each month, interest compounded monthly; rounded to the cent in the decimal value."] }) },
    { id: "present-value", re: new RegExp(String.raw`^how much (?:money )?(?:do (?:i|you|we) need to |must (?:i|you|we) |should (?:i|you|we) |would (?:i|you|we) have to )?(?:invest|deposit|save|put in|put away|put aside) (?:now |today )?(?:at|earning|with) (\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:per year|a year|annual(?:ly)?|interest|per annum|compounded annually))* to (?:have|get|reach|end up with|grow to|accumulate) ${AMT} (?:in|after) (\d+(?:\.\d+)?) years?$`, "i"),
      build: (m) => out(`${m[2]}/(1 + ${m[1]}/100)^${m[3]}`, `present value: PV = FV / (1 + r)^t with FV = ${m[2]}, r = ${m[1]}%, t = ${m[3]}`, { places: 2, notes: ["Interest compounded once a year; rounded to the cent in the decimal value."] }) },
    // ---- round 8: percent verbs, parity series, prime products, roots and logs by name, hands of cards, degree/radian
    //      conversions, squares from area, compound growth said plainly, bases by name, perfect squares, triangular
    //      numbers, digit tricks (each one is written as arithmetic the engine then evaluates and checks) ----
    { id: "speed-plain", re: /^(?:what is |what's |find |calculate )?(?:the |my |its |his |her |their )?(?:average )?speed(?: (?:if|when|for|of|to (?:travel|cover|drive|go|run|walk|cycle|fly)|travelling|traveling|covering|driving|going))?:? ?(?:i |you |we |a car |a train |a bus |a bike |a plane |a runner |a cyclist |it |someone |he |she |they )?(?:travel(?:s|led|ed)? |cover(?:s|ed)? |drive(?:s)? |drove |go(?:es)? |went |run(?:s)? |ran |walk(?:s|ed)? |cycle(?:s|d)? |fl(?:y|ies|ew) )?(\d+(?:\.\d+)?) ?(km|kilometers?|kilometres?|miles?|mi|m|meters?|metres?|feet|ft) in (\d+(?:\.\d+)?) ?(hours?|hrs?|h|minutes?|mins?|min|seconds?|secs?|s)$/i,
      build: (m) => { if (!(+m[3] > 0)) return null; const du = /^(?:km|kilomet)/i.test(m[2]) ? "km" : /^mi/i.test(m[2]) ? "miles" : /^(?:m|met)/i.test(m[2]) ? "m" : "ft"; const tu = /^h/i.test(m[4]) ? "hour" : /^m/i.test(m[4]) ? "minute" : "second";
        return out(`${m[1]}/${m[3]}`, `speed = distance / time = ${m[1]} ${du} / ${m[3]} ${tu}${+m[3] === 1 ? "" : "s"}`, { notes: [`The answer is in ${du} per ${tu}.`] }); } },
    { id: "time-plain", re: /^(?:what is |what's |find |calculate |how long is )?(?:the )?(?:travel |journey |driving )?time (?:needed |taken |required |it takes |to take )?(?:to (?:travel|cover|drive|go|run|walk|cycle|fly|complete)|for|over) (\d+(?:\.\d+)?) ?(km|kilometers?|kilometres?|miles?|mi|m|meters?|metres?|feet|ft) at (\d+(?:\.\d+)?) ?(km\/h|kph|kmh|km\/hr|km per hour|kilometers per hour|kilometres per hour|mph|mi\/h|miles per hour|miles an hour|m\/s|meters per second|metres per second|ft\/s|feet per second)$/i,
      build: (m) => { const du = /^(?:km|kilomet)/i.test(m[2]) ? "km" : /^mi/i.test(m[2]) ? "miles" : /^(?:m|met)/i.test(m[2]) ? "m" : "ft"; const r = m[4].toLowerCase();
        const ru = /^(?:km|kilomet)/.test(r) ? "km" : /^(?:mph|mi|miles)/.test(r) ? "miles" : /^(?:m\/s|met)/.test(r) ? "m" : "ft"; if (ru !== du || !(+m[3] > 0)) return null; const tu = /(?:h|hour)$/.test(r) ? "hour" : "second";
        return out(`${m[1]}/${m[3]}`, `time = distance / speed = ${m[1]} ${du} / ${m[3]} ${du} per ${tu}`, { notes: [`The answer is in ${tu}s.`] }); } },
    { id: "distance-plain", re: /^(?:what is |what's |find |calculate |how far is )?(?:the )?distance (?:covered |travelled |traveled |driven |gone )?(?:at|for|in|over|going|travelling|traveling|driving at|moving at) (\d+(?:\.\d+)?) ?(km\/h|kph|kmh|km\/hr|km per hour|kilometers per hour|kilometres per hour|mph|mi\/h|miles per hour|miles an hour|m\/s|meters per second|metres per second|ft\/s|feet per second) (?:for|in|over|during) (\d+(?:\.\d+)?) ?(hours?|hrs?|h|minutes?|mins?|min|seconds?|secs?|s)$/i,
      build: (m) => { const r = m[2].toLowerCase(); const ru = /^(?:km|kilomet)/.test(r) ? "km" : /^(?:mph|mi|miles)/.test(r) ? "miles" : /^(?:m\/s|met)/.test(r) ? "m" : "ft"; const rt = /(?:h|hour)$/.test(r) ? "hour" : "second";
        const tu = /^h/i.test(m[4]) ? "hour" : /^m/i.test(m[4]) ? "minute" : "second";
        // the time is converted into the speed's time unit first (30 minutes at km/h is half an hour)
        const conv = tu === rt ? m[3] : rt === "hour" ? `(${m[3]}/${tu === "minute" ? 60 : 3600})` : tu === "minute" ? `(${m[3]}*60)` : `(${m[3]}*3600)`;
        return out(`${m[1]}*${conv}`, `distance = speed x time = ${m[1]} ${ru} per ${rt} x ${m[3]} ${tu}${+m[3] === 1 ? "" : "s"}${conv === m[3] ? "" : ` = ${m[1]} x ${conv} ${rt}s`}`, { notes: [`The answer is in ${ru}.`] }); } },
    { id: "percent-verb", re: new RegExp(String.raw`^(?:what is |what's |find )?\$?${WNUM} (increased|raised|marked up|decreased|reduced|lowered|marked down|discounted|cut) by ${WNUM} ?(?:%|percent|per cent)$`, "i"),
      build: (m) => { const up = /^(?:increased|raised|marked up)$/i.test(m[2]); return out(`${m[1]}*(1 ${up ? "+" : "-"} ${m[3]}/100)`, `${m[1]} ${up ? "increased" : "decreased"} by ${m[3]}%: ${m[1]} x (1 ${up ? "+" : "-"} ${m[3]}/100)`); } },
    { id: "parity-series", re: /^(?:what is |find |calculate )?(?:the )?sum of (?:all )?(?:the )?(even|odd) (?:numbers|integers|whole numbers) (?:from|between) (\d+) (?:to|and|through|up to) (\d+)(?: inclusive)?$/i,
      build: (m) => { const odd = /odd/i.test(m[1]); let a = +m[2], b = +m[3]; if (a > b || b > 1e9) return null;
        if ((a % 2 === 1) !== odd) a++; if ((b % 2 === 1) !== odd) b--; if (a > b) return null; const n = (b - a) / 2 + 1;
        return out(`sum(${a} + 2k, k, 0, ${n - 1})`, `${m[1].toLowerCase()} numbers ${a}, ${a + 2}, ..., ${b}: ${n} terms of an arithmetic series`); } },
    { id: "parity-series", re: /^(?:what is |find |calculate )?(?:the )?sum of (?:the )?first (\d+) (even|odd) (?:numbers|integers|whole numbers|positive integers|natural numbers)$/i,
      build: (m) => { const n = +m[1]; if (!(n >= 1 && n <= 1e9)) return null; const odd = /odd/i.test(m[2]);
        return out(odd ? `sum(2k - 1, k, 1, ${n})` : `sum(2k, k, 1, ${n})`, `the first ${n} ${odd ? "odd" : "even"} numbers ${odd ? "1, 3, 5, ..." : "2, 4, 6, ..."}: sum of ${odd ? "2k - 1" : "2k"} for k = 1..${n}`); } },
    { id: "first-primes", re: /^(?:what is |find |calculate )?(?:the )?(sum|product) of (?:the )?first (\d+) primes?(?: numbers?)?$/i,
      build: (m) => { const n = +m[2]; if (!(n >= 1 && n <= 60)) return null; const ps = []; for (let k = 2; ps.length < n; k++) if (isPrimeN(k)) ps.push(k);
        const op = /sum/i.test(m[1]) ? " + " : "*"; return out(ps.join(op), `the first ${n} primes are ${ps.join(", ")}; their ${m[1].toLowerCase()} is ${ps.join(op === "*" ? " x " : " + ")}`); } },
    { id: "is-perfect", re: /^is (\d+) (?:a )?perfect(?: number)?$/i,
      build: (m) => { const n = +m[1]; if (!(n >= 1 && n <= 1e12)) return null; return out(`divisorsum(${n}) - ${n} = ${n}`, `${n} is perfect when its proper divisors (all divisors except ${n} itself) add up to ${n}`, { goal: "evaluate" }); } },
    { id: "is-palindrome", re: /^is (\d+) (?:a )?(?:numeric |numerical |number )?palindrome(?: number| numeral)?$/i,
      build: (m) => { const s = m[1]; if (s.length > 60) return null; const r = [...s].reverse().join(""); return out(`${s} = ${r}`, `${s} read backwards is ${r}; a palindrome reads the same both ways`, { goal: "evaluate" }); } },
    { id: "nth-root", re: /^(?:what is |what's |find |calculate |compute )?(?:the )?(\d+)(?:st|nd|rd|th)[- ]root of (.+)$/i,
      build: (m) => { const n = +m[1], x = E(m[2]); if (!(n >= 2 && n <= 1000) || !x) return null; return out(`root(${x}, ${n})`, `the ${m[1]}${{ 1: "st", 2: "nd", 3: "rd" }[m[1] % 10 === 1 && m[1] % 100 !== 11 ? 1 : m[1] % 10 === 2 && m[1] % 100 !== 12 ? 2 : m[1] % 10 === 3 && m[1] % 100 !== 13 ? 3 : 0] || "th"} root of ${x} (${x}^(1/${n}))`); } },
    { id: "nth-root", re: /^(?:what is |what's |find |calculate |compute )?(?:the )?(fourth|fifth|sixth|seventh|eighth|ninth|tenth)[- ]root of (.+)$/i,
      build: (m) => { const n = { fourth: 4, fifth: 5, sixth: 6, seventh: 7, eighth: 8, ninth: 9, tenth: 10 }[m[1].toLowerCase()], x = E(m[2]); if (!x) return null; return out(`root(${x}, ${n})`, `the ${m[1].toLowerCase()} root of ${x} (${x}^(1/${n}))`); } },
    { id: "log-named-base", re: /^(?:what is |what's |find |calculate |compute )?(?:the )?log[_ ]?(\d+) (?:of )?(.+)$/i,
      build: (m) => { const b = +m[1], x = E(m[2]); if (!(b >= 2) || !x) return null; return out(`log(${b}, ${x})`, `log base ${b} of ${x}`); } },
    { id: "card-hands", re: /^how many (?:different |distinct |possible )?(\d+)[- ]card hands (?:can be dealt |can you (?:be dealt|make|draw|get) |are there |are possible |can be drawn |can be made )?(?:from|in|out of|using|with) (?:a |an )?(?:standard |ordinary |regular |full |single )?(?:deck of )?(\d+)(?:[- ]card)?(?: cards| deck| card deck| playing cards)?$/i,
      build: (m) => { const k = +m[1], n = +m[2]; if (!(k >= 1 && n >= k && n <= 1000)) return null; return out(`binomial(${n}, ${k})`, `unordered hands: choose ${k} of ${n} cards, C(${n}, ${k})`); } },
    { id: "to-degrees", re: /^(?:convert |what is |what's |express |write |give )?(.+?)(?: rad(?:ian)?s?)? (?:in|to|as|into) degrees$/i,
      build: (m) => { const x = E(m[1]); if (!x || /[a-z]/i.test(x.replace(/\b(?:pi|e|sqrt|cbrt|sin|cos|tan|asin|acos|atan|arcsin|arccos|arctan|ln|log|abs|root|exp)\b/gi, "")) || /\bdegrees?\b|\bdeg\b|°/i.test(m[1])) return null;
        return out(`(${x})*180/pi`, `${x} radians x 180/pi`, { notes: ["The answer is in degrees."] }); } },
    { id: "to-radians", re: /^(?:convert |what is |what's |express |write |give )?(.+?) (?:degrees?|deg|°) (?:in|to|as|into) rad(?:ian)?s?$/i,
      build: (m) => { const x = E(m[1]); if (!x || /[a-z]/i.test(x.replace(/\b(?:sqrt|cbrt)\b/gi, ""))) return null; return out(`(${x})*pi/180`, `${x} degrees x pi/180`, { notes: ["The answer is in radians."] }); } },
    { id: "square-from", re: /^(?:what is |what's |find |calculate )?(?:the )?(side|side length|perimeter|area|diagonal) of a square (?:with|whose|of|that has|having) (?:an? )?(area|perimeter|side|side length|diagonal)(?: is| of| equal to| equals| =)? \$?(\d+(?:\.\d+)?)(?: (?:square )?(?:cm|m|mm|km|in|inches|ft|feet|units?|meters?|metres?))?(?: squared)?$/i,
      build: (m) => { const want = m[1].toLowerCase().replace(" length", ""), from = m[2].toLowerCase().replace(" length", ""), v = m[3]; if (want === from) return null;
        const side = { side: v, perimeter: `${v}/4`, area: `sqrt(${v})`, diagonal: `${v}/sqrt(2)` }[from];
        const outOf = { side: (s) => s, perimeter: (s) => `4*(${s})`, area: (s) => `(${s})^2`, diagonal: (s) => `(${s})*sqrt(2)` }[want];
        return out(outOf(side), `side = ${side} (from the ${from} ${v})${want === "side" ? "" : `; ${want} = ${outOf("side")}`}`); } },
    { id: "compound-plain", re: new RegExp(String.raw`^(?:what is |what's |how much is |find )?(?:the )?(?:value of |amount of |worth of )?${AMT} (?:invested |deposited |saved |put away |placed )?at (\d+(?:\.\d+)?) ?(?:%|percent)(?: (?:interest|per year|a year|annual(?:ly)?|per annum|apr))*,? (?:compounded (annually|yearly|semi-?annually|quarterly|monthly|weekly|daily) (?:for|over|after) (\d+(?:\.\d+)?) years?|(?:for|over|after) (\d+(?:\.\d+)?) years? compounded (annually|yearly|semi-?annually|quarterly|monthly|weekly|daily))$`, "i"),
      build: (m) => { const f = { annually: 1, yearly: 1, semiannually: 2, "semi-annually": 2, quarterly: 4, monthly: 12, weekly: 52, daily: 365 }[(m[3] || m[6]).toLowerCase()], t = m[4] || m[5]; if (!f) return null;
        return out(f === 1 ? `${m[1]}*(1 + ${m[2]}/100)^${t}` : `${m[1]}*(1 + ${m[2]}/(100*${f}))^(${f}*${t})`, `A = P (1 + r/n)^(n t) with P = ${m[1]}, r = ${m[2]}%, n = ${f}, t = ${t}`, { places: 2, notes: ["Rounded to the cent in the decimal value."] }); } },
    { id: "base-by-name", re: /^(?:what is |what's |find |give |show )?(?:the )?(binary|octal|hex|hexadecimal|base[- ]?(\d+)) (?:form|representation|version|value|equivalent|notation|expansion)? ?(?:of|for) (\d+)$/i,
      build: (m) => { const b = m[2] ? +m[2] : { binary: 2, octal: 8, hex: 16, hexadecimal: 16 }[m[1].toLowerCase()]; if (!(b >= 2 && b <= 36) || m[3].length > 60) return null; return out(`tobase(${m[3]}, ${b})`, `${m[3]} written in base ${b}`); } },
    { id: "base-by-name", re: /^(?:convert |what is |what's )?(?:the )?(binary|octal|hex|hexadecimal) (?:number |value )?([0-9a-f]+) (?:to|in|into|as) (?:decimal|denary|base[- ]?10|a (?:decimal )?number)$/i,
      build: (m) => { const b = { binary: 2, octal: 8, hex: 16, hexadecimal: 16 }[m[1].toLowerCase()]; const digits = m[2].toLowerCase(); if ([...digits].some((c) => !(parseInt(c, 36) < b)) || digits.length > 60) return null;
        const vals = [...digits].map((c) => parseInt(c, 36)); return out(vals.map((d, i) => `${d}*${b}^${vals.length - 1 - i}`).join(" + "), `positional value of ${digits} in base ${b}`); } },
    { id: "next-square", re: /^(?:what is |what's |find )?(?:the )?(next|smallest|first|largest|biggest|greatest|previous|last|nearest|closest) perfect (square|cube)(?: number)? (after|above|greater than|bigger than|larger than|more than|over|before|below|less than|smaller than|under|to) (\d+)$/i,
      build: (m) => { const n = +m[1 + 3], cube = /cube/i.test(m[2]); if (!(n >= 0 && n <= 1e15)) return null; const p = cube ? 3 : 2, rt = (v) => Math.round(Math.pow(v, 1 / p));
        const near = /nearest|closest/i.test(m[1]) || /^to$/i.test(m[3]); const up = /next|smallest|first/i.test(m[1]) || /after|above|greater|bigger|larger|more|over/i.test(m[3]);
        if (near !== /^to$/i.test(m[3])) return null; let k;
        if (near) { let lo = rt(n); while (lo ** p > n) lo--; while ((lo + 1) ** p <= n) lo++; k = n - lo ** p <= (lo + 1) ** p - n ? lo : lo + 1; }
        else if (up) { k = rt(n); while (k ** p <= n) k++; while ((k - 1) ** p > n) k--; }
        else { k = rt(n); while (k ** p >= n) k--; while ((k + 1) ** p < n) k++; if (k < 0) return null; }
        return out(`${k}^${p}`, `${k}^${p} = ${k ** p} is the ${near ? "nearest" : up ? "smallest" : "largest"} perfect ${cube ? "cube" : "square"} ${near ? "to" : up ? "above" : "below"} ${n}${near ? "" : ` (${up ? k - 1 : k + 1}^${p} = ${(up ? k - 1 : k + 1) ** p} is ${up ? "not above" : "not below"} it)`}`); } },
    { id: "triangular", re: /^(?:what is |what's |find )?(?:the )?(\d+)(?:st|nd|rd|th) triangular number$/i,
      build: (m) => { const n = +m[1]; return n >= 1 && n <= 1e12 ? out(`${n}*(${n} + 1)/2`, `T(${n}) = 1 + 2 + ... + ${n} = n(n + 1)/2`) : null; } },
    { id: "digit-sum", re: /^(?:what is |what's |find )?(?:the )?(?:digit sum|digital sum|sum of (?:the |its )?digits) (?:of|in) (\d+)(?:\^| to the (?:power of )?| \*\* )(\d+)$/i,
      build: (m) => { const a = BigInt(m[1]), b = +m[2]; if (b > 20000 || a < 0n) return null; const d = (a ** BigInt(b)).toString(); if (d.length > 400) return out(String([...d].reduce((s, c) => s + +c, 0)), `${m[1]}^${m[2]} has ${d.length} digits; their sum was added up exactly`, { notes: ["Computed exactly from the full power."] });
        return out(d.split("").join(" + "), `${m[1]}^${m[2]} = ${d}; add its digits`); } },
    { id: "digit-sum", re: /^(?:what is |what's |find )?(?:the )?(?:digit sum|digital sum) of (\d+)$/i, build: (m) => out(m[1].split("").join(" + "), `digits of ${m[1]}: ${m[1].split("").join(" + ")}`) },
    { id: "reverse-digits", re: /^(?:what is |what's |find )?(?:reverse (?:the digits of )?|(?:the )?(?:digits of )?)?(\d+) (?:reversed|backwards|with (?:its|the) digits reversed)$|^reverse (?:the )?(?:digits (?:of|in) )?(\d+)$/i,
      build: (m) => { const s = (m[1] || m[2]); if (s.length > 60) return null; const r = [...s].reverse().join(""); const terms = [...r].map((c, i) => (i === r.length - 1 ? c : `${c}*10^${r.length - 1 - i}`));
        return out(terms.join(" + "), `${s} reversed is ${r}: ${terms.join(" + ")}`, { notes: /0$/.test(s) ? ["Trailing zeros of the original become leading zeros and drop away."] : [] }); } },
  ];
}
// "2 + 5 + 8 + ... + 32": the listed terms fix the pattern (arithmetic or geometric), the last term fixes the count
function finiteSeries(t, L, out) {
  if (t.length < 3 || !t.every(Number.isInteger) || !Number.isInteger(L)) return null;
  const d = t[1] - t[0];
  if (t.every((v, i) => i === 0 || v - t[i - 1] === d) && d !== 0) { const n = (L - t[0]) / d + 1; if (!Number.isInteger(n) || n < t.length) return null;
    return out(`${n}*(${t[0]} + ${L})/2`, `arithmetic series: ${n} terms from ${t[0]} to ${L} with difference ${d}, sum n (first + last)/2`); }
  if (t[0] !== 0 && t[1] % t[0] === 0) { const r = t[1] / t[0]; if (Math.abs(r) < 2 || !t.every((v, i) => i === 0 || v === t[i - 1] * r)) return null;
    let n = 1, v = t[0]; while (v !== L && Math.abs(v) <= Math.abs(L) && n < 200) { v *= r; n++; } if (v !== L || n < t.length) return null;
    return out(`sum(${t[0]}*(${r})^k, k, 0, ${n - 1})`, `geometric series: ${n} terms, first ${t[0]}, ratio ${r}, last ${L}`); }
  return null;
}
// mixed units of one dimension: "3 hours 25 minutes in minutes", "5 feet 10 inches in inches"
const MIXED = { week: ["time", 604800], wk: ["time", 604800], day: ["time", 86400], hour: ["time", 3600], hr: ["time", 3600], hrs: ["time", 3600], h: ["time", 3600], minute: ["time", 60], min: ["time", 60], second: ["time", 1], sec: ["time", 1], s: ["time", 1],
  foot: ["imperial", 12], feet: ["imperial", 12], ft: ["imperial", 12], inch: ["imperial", 1], inche: ["imperial", 1], in: ["imperial", 1], yard: ["imperial", 36], yd: ["imperial", 36], yds: ["imperial", 36],
  pound: ["weight", 16], lb: ["weight", 16], lbs: ["weight", 16], ounce: ["weight", 1], oz: ["weight", 1],
  kilometer: ["metric", 100000], kilometre: ["metric", 100000], km: ["metric", 100000], meter: ["metric", 100], metre: ["metric", 100], m: ["metric", 100], centimeter: ["metric", 1], centimetre: ["metric", 1], cm: ["metric", 1] };
const mixedUnit = (w) => MIXED[String(w).toLowerCase().replace(/(?<=[a-z]{3})s$/, "")] || null;
function mixedUnits(A, ua, B, ub, ut, out) {
  const a = mixedUnit(ua), b = mixedUnit(ub), t = mixedUnit(ut);
  if (!a || !b || !t || a[0] !== b[0] || a[0] !== t[0] || a[1] <= b[1]) return null; // the bigger unit is said first
  const total = `${A}*${a[1] / b[1]} + ${B}`; // in the smaller unit
  const math = t[1] === b[1] ? total : t[1] < b[1] ? `(${total})*${b[1] / t[1]}` : `(${total})/${t[1] / b[1]}`;
  return out(math, `${A} ${ua} ${B} ${ub}: ${A} x ${a[1] / b[1]} ${ub} + ${B} ${ub}${t[1] === b[1] ? "" : `, then to ${ut}`}`, { notes: [`In ${ut}.`] });
}
// dot-product angle between two vectors of the same length
function vectorAngle(a, b, degrees, out) {
  const xs = a.split(/\s*,\s*/), ys = b.split(/\s*,\s*/);
  if (xs.length !== ys.length || xs.length < 2 || xs.every((v) => +v === 0) || ys.every((v) => +v === 0)) return null;
  const dot = xs.map((x, i) => `(${x})*(${ys[i]})`).join(" + "), na = xs.map((x) => `(${x})^2`).join(" + "), nb = ys.map((y) => `(${y})^2`).join(" + ");
  const rad = `acos((${dot})/(sqrt(${na})*sqrt(${nb})))`;
  return out(degrees ? `(${rad})*180/pi` : rad, `cos(theta) = (a . b)/(|a| |b|) with a . b = ${dot}`, { notes: [degrees ? "The angle is in degrees." : "The angle is in radians; add \"in degrees\" for degrees."] });
}
function profitOf(kind, pct, cost, sell) {
  const d = +sell - +cost, loss = /loss/i.test(kind);
  if ((loss && d > 0) || (!loss && d < 0)) return null; // asked for a profit on a sale at a loss (or the reverse): do not flip the sign silently
  const diff = loss ? `${cost} - ${sell}` : `${sell} - ${cost}`;
  return pct ? { math: `(${diff})/${cost}*100`, interpretation: `${loss ? "loss" : "profit"} percent = (${diff}) / cost ${cost} x 100`, notes: ["The answer is in percent."] }
    : { math: diff, interpretation: `${loss ? "loss" : "profit"} = ${diff}` };
}

export function morePatterns({ expr, mathOf, LEAD, re }) {
  const E = (s) => mathOf(s) || null;
  const out = (math, interpretation, extra = {}) => (math ? { math, interpretation, ...extra } : null);
  // substitute a value for one variable in math text: 3x^2 + 2 at x = 4 -> 3(4)^2 + 2 (a letter inside a
  // function name such as the x of exp is left alone)
  const subst = (body, v, val) => body.replace(new RegExp(`(?<![A-Za-z_])${v}(?![A-Za-z_(])`, "g"), `(${val})`);
  // exact rational of a simple term ("1", "1/2", "0.25", "-3/4") as [numerator, denominator] BigInts
  const ratOf = (s) => { const m = /^\s*(-?\d+)(?:\.(\d+))?(?:\s*\/\s*(\d+))?\s*$/.exec(s); if (!m) return null;
    let n = BigInt(m[1] + (m[2] || "")), d = 10n ** BigInt((m[2] || "").length) * BigInt(m[3] || 1); return d === 0n ? null : [n, d]; };
  const DIE = { even: [2, 4, 6], odd: [1, 3, 5], prime: [2, 3, 5] };
  return [
    // ---- everyday phrasings (plain percent changes, fraction forms, "evaluate ... when x = 4") ----
    ...everydayPatterns({ E, out, WN }),
    { id: "percent-change-by", re: /^(?:what is |find |calculate )?(increase|raise|decrease|reduce|lower|cut|discount) \$?(\S+?) by (\S+?) ?(?:%|percent|per cent)$/i,
      build: (m) => { const x = E(m[2]), p = E(m[3]); if (!x || !p) return null; const up = /^(increase|raise)$/i.test(m[1]);
        return out(`${x}*(1 ${up ? "+" : "-"} ${p}/100)`, `${x} ${up ? "increased" : "decreased"} by ${p}%: ${x} x (1 ${up ? "+" : "-"} ${p}/100)`); } },
    { id: "percent-more-than", re: /^(?:what is |find )?(\S+?) ?(?:%|percent) (more|less|greater|smaller|higher|lower) than \$?(\S+)$/i,
      build: (m) => { const p = E(m[1]), x = E(m[3]); if (!x || !p) return null; const up = /more|greater|higher/i.test(m[2]);
        return out(`${x}*(1 ${up ? "+" : "-"} ${p}/100)`, `${p}% ${up ? "more" : "less"} than ${x}: ${x} x (1 ${up ? "+" : "-"} ${p}/100)`); } },
    { id: "as-decimal", re: /^(?:write |convert |express |change |turn |what is )?(.+?) (?:as|to|into|in) (?:a )?decimal(?: form| number)?$/i,
      build: (m) => { if (/\b(?:binary|hex|octal|base|ternary)\b|0[xbo]|_\d|^[0-9a-f]*[a-f][0-9a-f]*$/i.test(m[1].trim())) return null; const x = E(m[1]); return x ? out(x, `${x} as a decimal`, { notes: ["The decimal value is shown next to the exact one."] }) : null; } },
    { id: "as-percent", re: /^(?:write |convert |express |change |turn |what is )?(.+?) (?:as|to|into|in) (?:a )?percent(?:age)?$/i,
      build: (m) => { const x = E(m[1]); return x ? out(`(${x})*100`, `${x} as a percent: ${x} x 100`, { notes: ["The answer is in percent."] }) : null; } },
    { id: "reciprocal", re: /^(?:what is |find )?(?:the )?(?:reciprocal|multiplicative inverse) of (.+)$/i,
      build: (m) => { const x = E(m[1]); return x ? out(`1/(${x})`, `reciprocal of ${x}: 1/(${x})`) : null; } },
    { id: "fib-nth", re: /^(?:what is |find |give me )?(?:the )?(\d+)(?:st|nd|rd|th)? fibonacci(?: number| term)?$/i,
      build: (m) => +m[1] <= 5000 ? out(`fibonacci(${m[1]})`, `Fibonacci number F(${m[1]}), with F(1) = F(2) = 1`) : null },
    { id: "eval-at", re: /^(?:evaluate|find|compute|calculate|what is|what's|work out)? ?(?:the value of )?(.+?),? (?:when|at|for|if|where|given) ([a-z]) ?= ?(-?[\d./]+)$/i,
      build: (m) => { const body = E(m[1]); if (!body || /[=<>]/.test(body) || !new RegExp(`(?<![A-Za-z_])${m[2]}(?![A-Za-z_(])`).test(body)) return null;
        return out(subst(body, m[2], m[3]), `${body} with ${m[2]} = ${m[3]}`); } },
    { id: "fn-value", re: /^(?:if |given |given that |let |suppose )?([a-z])\(([a-z])\) ?= ?(.+?)[,.;:]? (?:then )?(?:find|what is|what's|evaluate|compute|calculate|and) \1\((-?[\d./]+)\)$/i,
      build: (m) => { const body = E(m[3]); if (!body || /[=<>]/.test(body)) return null; return out(subst(body, m[2], m[4]), `${m[1]}(${m[4]}) for ${m[1]}(${m[2]}) = ${body}`); } },
    // the value first: "f(3) if f(x) = x^2 + 1", "what is g(2) when g(t) = 3t - 1"
    { id: "fn-value", re: /^(?:find |what is |what's |evaluate |compute |calculate )?([a-z])\((-?[\d./]+)\),? (?:if|when|where|given|given that|for|with) \1\(([a-z])\) ?= ?(.+)$/i,
      build: (m) => { const body = E(m[4]); if (!body || /[=<>]/.test(body)) return null; return out(subst(body, m[3], m[2]), `${m[1]}(${m[2]}) for ${m[1]}(${m[3]}) = ${body}`); } },
    { id: "solve-trailing", re: /^(.+?[=<>].*?)[,.;:]? (?:find|solve for|what is|what's|determine) ([a-z])$/i,
      build: (m) => { const t = expr(m[1]); if (!/[=<>]/.test(t) || !new RegExp(`(?<![A-Za-z_])${m[2]}(?![A-Za-z_(])`).test(t)) return null; return { math: t, goal: "solve", variable: m[2], interpretation: `solve ${t} for ${m[2]}` }; } },
    { id: "geo-series-sum", re: /^(?:(?:find |what is |compute |calculate )?(?:the )?sum of (?:the )?(?:infinite )?(?:geometric )?(?:series|sequence)?:? ?)?(.+?)\s*\+\s*(?:\.\.\.|…)?(?:\s*(?:to infinity|to oo|forever|and so on(?: forever)?|etc\.?))?$/i,
      build: (m) => {
        const terms = m[1].split(/\s*\+\s*/).map(ratOf);
        if (terms.length < 3 || terms.some((t) => !t) || terms[0][0] === 0n) return null;
        // common ratio r = t1/t0, checked on every later pair
        const [a, b] = terms; const rn = b[0] * a[1], rd = b[1] * a[0];
        for (let i = 1; i + 1 < terms.length; i++) { const [p, q] = terms[i], [s, t] = terms[i + 1]; if (s * q * rd !== rn * t * p) return null; }
        const fr = (n, d) => { const g = (x, y) => (y ? g(y, x % y) : x < 0n ? -x : x), k = g(n, d) || 1n, s = d < 0n ? -1n : 1n; return (d / k) * s === 1n ? `${(n / k) * s}` : `${(n / k) * s}/${(d / k) * s}`; };
        const a0 = fr(a[0], a[1]), r = fr(rn, rd);
        return out(`sum((${a0})*(${r})^n, n, 0, oo)`, `geometric series with first term ${a0} and ratio ${r}`);
      } },
    { id: "prob-die-kind", re: /^(?:what is )?(?:the )?(?:probability|chance) (?:of )?(?:rolling|getting|throwing) (?:an? )?(even|odd|prime) (?:number )?(?:on|with) (?:a |one )?(?:fair |single |standard |six[- ]sided |regular )*(?:die|dice)$/i,
      build: (m) => { const f = DIE[m[1].toLowerCase()]; return out(`${f.length}/6`, `a fair die: ${f.length} of 6 faces (${f.join(", ")}) are ${m[1].toLowerCase()}`); } },
    { id: "prob-die-cmp", re: /^(?:what is )?(?:the )?(?:probability|chance) (?:of )?(?:rolling|getting|throwing) (?:a (?:number )?)?(greater than|more than|higher than|less than|lower than|at least|at most) (\d) (?:on|with) (?:a |one )?(?:fair |single |standard |six[- ]sided |regular )*(?:die|dice)$/i,
      build: (m) => { const k = +m[2], c = m[1].toLowerCase(); const faces = [1, 2, 3, 4, 5, 6].filter((v) => /greater|more|higher/.test(c) ? v > k : /less|lower/.test(c) ? v < k : c === "at least" ? v >= k : v <= k);
        return out(`${faces.length}/6`, `a fair die: ${faces.length} of 6 faces (${faces.join(", ") || "none"}) qualify`); } },
    { id: "prob-coin-run", re: /^(?:what (?:is|are) )?(?:the )?(probability|chance|odds) (?:of )?(?:flipping|getting|tossing|throwing)? ?(?:(two|three|four|five|six|\d+) (heads|tails)(?: in a row)?|(heads|tails) (twice|three times|(two|three|four|five|\d+) times)(?: in a row)?)$/i,
      build: (m) => { const W = { two: 2, three: 3, four: 4, five: 5, six: 6, twice: 2, "three times": 3 };
        const k = m[2] ? (W[m[2].toLowerCase()] || +m[2]) : (W[m[5].toLowerCase()] || W[(m[6] || "").toLowerCase()] || +m[6]);
        if (!(k >= 1 && k <= 60)) return null; const side = (m[3] || m[4]).toLowerCase();
        const notes = /odds/i.test(m[1]) ? [`Read "odds" as a probability; as odds against it is ${2 ** k - 1} : 1.`] : [];
        return out(`(1/2)^${k}`, `${k} fair coin flips, all ${side}: (1/2)^${k}`, { notes }); } },
    { id: "sales-tax", re: /^(?:what is |how much is |find |calculate )?(?:the )?(?:sales )?tax (?:on|for) (?:a |an |the )?\$?(\d+(?:\.\d+)?)(?: dollars?| bucks| euros?| pounds?)?(?: [a-z]+)? (?:at|with) (?:a )?(\d+(?:\.\d+)?) ?(?:%|percent)(?: tax| rate| tax rate| sales tax)?$/i,
      build: (m) => out(`${m[2]}/100*${m[1]}`, `tax = ${m[2]}% of ${m[1]}`) },
    { id: "sales-tax", re: /^(?:what is |how much is |find |calculate )?(?:the )?(?:total|total cost|final price|price) (?:of |for )?(?:a |an |the )?\$?(\d+(?:\.\d+)?)(?: dollars?| bucks| euros?| pounds?)?(?: [a-z]+)? (?:with|after|including|plus) (?:a )?(\d+(?:\.\d+)?) ?(?:%|percent) (?:sales )?tax$/i,
      build: (m) => out(`${m[1]}*(1 + ${m[2]}/100)`, `price plus ${m[2]}% tax: ${m[1]} x (1 + ${m[2]}/100)`) },
    { id: "age-times-later", re: /^(\w+) is (twice|three times|four times|five times|(\d+) times) as old as (?:his|her|their) (son|daughter|child|brother|sister|niece|nephew|grandson|granddaughter)\. in (\d+) years,? (?:he|she|they|\1) will (?:only )?be (twice|three times|four times|(\d+) times) as old(?: as (?:his|her|their) \4)?\. how old is (?:the|his|her|their) \4(?: now)?$/i,
      build: (m) => { const W = { twice: 2, "three times": 3, "four times": 4, "five times": 5 };
        const k1 = W[m[2].toLowerCase()] || +m[3], k2 = W[m[6].toLowerCase()] || +m[7], t = m[5];
        if (!(k1 > k2 && k2 > 1)) return null; // otherwise no positive age satisfies it
        const eqn = `${k1}y + ${t} = ${k2}(y + ${t})`;
        return { math: eqn, goal: "solve", variable: "y", interpretation: `let y be the ${m[4]}'s age now (${m[1]} is ${k1}y): ${eqn}` }; } },
    // ---------------------------------------------------------------- probability
    { id: "prob-die", re: /^(?:what is )?(?:the )?probability (?:of )?(?:rolling|getting|throwing) (?:a|an) (\d) (?:on|with) (?:a |one )?(?:fair |single |standard |six[- ]sided )*(?:die|dice)$/i,
      build: (m) => (+m[1] >= 1 && +m[1] <= 6 ? out("1/6", `one favourable face out of 6 equally likely faces: 1/6`) : null) },
    { id: "prob-dice-sum", re: /^(?:what is )?(?:the )?probability (?:of )?(?:rolling|getting|throwing) (?:a (?:sum|total) of |a total |a |an )?(\d+)(?: as the (?:sum|total))? (?:with|on|using) (?:two|2|a pair of) (?:fair )?dice$/i,
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
    { id: "series-finite", re: /^(?:find |what is )?(?:the )?(?:sum of (?:the )?)?(?:first (\w+) terms of (?:the )?)?(?:(arithmetic|geometric) (?:series|sequence|progression):? ?|(?:series|sequence|progression):? ?)?(-?\d[\d./]*(?:\s*(?:,|\+)\s*-?\d[\d./]*){2,})(?:\s*(?:,|\+)?\s*(?:\.{1,3}|…)?)?(?:,? ?(?:to |with |for )?(\w+) terms)?$/i,
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
    { id: "geo-solid", re: re(`^${LEAD}(volume|surface area) (?:of )?(?:a |the )?(sphere|ball|hemisphere),? (?:(?:with|of|whose|having) (?:a )?)?(radius|diameter|r|d)(?: is| of| =)? ?${num}(?: ?\\w+)?$`),
      build: (m) => {
        const r = /^d/i.test(m[3]) ? `(${m[4]})/2` : m[4], vol = /vol/i.test(m[1]), hemi = /hemi/i.test(m[2]);
        if (hemi) return out(vol ? `2*pi*(${r})^3/3` : `3*pi*(${r})^2`, vol ? "hemisphere volume (2/3) pi r^3" : "hemisphere total surface area 3 pi r^2 (curved 2 pi r^2 plus the flat disc)");
        return out(vol ? `4*pi*(${r})^3/3` : `4*pi*(${r})^2`, vol ? "sphere volume (4/3) pi r^3" : "sphere surface area 4 pi r^2");
      } },
    { id: "geo-solid", re: re(`^${LEAD}(volume|surface area|lateral surface area|curved surface area) (?:of )?(?:a |the )?(?:right )?(?:circular )?(cylinder|cone),? (?:(?:with|of|whose|having) )?(?:a )?radius(?: of| is| =)? ?${num}(?: ?\\w+)?(?:,? and|,)? (?:a )?height(?: of| is| =)? ?${num}(?: ?\\w+)?$`),
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
    { id: "geo-angles", re: re(`^${LEAD}(sum of (?:the )?(?:interior )?angles|(?:interior )?angle sum|(?:each|one) interior angle|(?:each|one) exterior angle|sum of (?:the )?exterior angles|how many degrees(?: are)?(?: there)?|(?:each|one) angle|(?:an |the )?interior angle|(?:an |the )?exterior angle|(?:the )?(?:measure|size) of (?:each|one) (?:interior )?angle) (?:of|in) (?:a |an |each |one )?(regular |equilateral )?([\\w -]+?)$`),
      build: (m) => {
        const n = sidesOf(m[3]);
        if (!n) return null;
        let q = m[1].toLowerCase();
        if (/^how many degrees/.test(q)) q = "sum of interior angles";
        // "each angle" / "the interior angle" only has one value when the polygon is regular
        if (/^(?:(?:an |the )?(?:interior|exterior) angle|(?:each|one) angle|(?:the )?(?:measure|size) of)/.test(q)) { if (!m[2]) return null; q = /exterior/.test(q) ? "each exterior angle" : "each interior angle"; }
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
    { id: "compound", re: /^(?:find (?:the )?|what is (?:the )?|calculate (?:the )?)?compound interest( (?:earned )?on)?:? \$?([\d,.]+) (?:dollars )?at ([\d.]+) ?%(?: (?:per year|a year|annually|p\.?a\.?))?(?: compounded (annually|yearly|semi-?annually|quarterly|monthly|weekly|daily|continuously))? for ([\d.]+) years?$/i,
      build: (m) => {
        const on = !!m[1], P = m[2].replace(/,/g, ""), r = m[3], t = m[5], how = (m[4] || "annually").toLowerCase();
        const A = how === "continuously" ? `${P}*e^(${r}/100*${t})` : null;
        const n = { annually: 1, yearly: 1, semiannually: 2, "semi-annually": 2, quarterly: 4, monthly: 12, weekly: 52, daily: 365 }[how];
        const amt = A || `${P}*(1 + ${r}/100/${n})^(${n}*${t})`, how2 = A ? `continuous compounding: A = P e^(rt) with P = ${P}, r = ${r}%, t = ${t}` : `A = P (1 + r/n)^(nt) with P = ${P}, r = ${r}%, n = ${n} per year, t = ${t}`;
        // "compound interest on P" asks for the interest earned, A - P
        if (on) return out(`${amt} - ${P}`, `compound interest = A - P, ${how2}`, { notes: m[4] ? [] : ["Compounded once a year (no period was given)."] });
        return out(amt, how2, { notes: ["This is the final amount; the interest earned is this minus the principal."] });
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
    // "sqrt 2 to 10 decimal places", "pi to 50 digits": the sentence sets the precision; the engine still computes with a proven error bound
    { id: "precision", re: /^(?:what is |compute |calculate |give |give me |show |show me |find |evaluate |value of )?(.+?) (?:to|with|correct to|accurate to) (\d+|[a-z]+) (decimal places?|decimals?|dp|d\.p\.|places|digits|significant figures|significant digits|sig figs|s\.f\.)$/i,
      build: (m) => { const x = E(m[1]), n = nOf(m[2]); if (!x || !/^\d+$/.test(n) || +n < 1 || +n > 1000 || /[=<>]/.test(x)) return null;
        if (/[a-df-z]/i.test(x.replace(/sqrt|cbrt|pi|sinh|cosh|tanh|sin|cos|tan|ln|log|exp|arcsin|arccos|arctan|asin|acos|atan|abs/gi, ""))) return null; // a constant, not a formula in x
        const places = /decimal|dp|d\.p|places/i.test(m[3]);
        return out(x, `${x} to ${n} ${places ? "decimal place" : "significant digit"}${+n === 1 ? "" : "s"}`, places ? { places: +n } : { digits: +n }); } },
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
    { id: "unit-rate", re: /^(?:if )?(\S+) (\w+) costs? \$?([\d.]+)(?: dollars)?,? (?:then )?how much (?:do|does|would|will) (\S+)(?: \2| of them)? cost$/i,
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
    // point-slope: "line through (0, 1) with slope 2", "line with slope 2 through (0, 1)", "line with slope 2 and y-intercept 3"
    { id: "line-slope", re: re(`^${LEAD}(?:equation (?:of|for) )?(?:the )?(?:straight )?line (?:through|passing through|that passes through|containing|going through) (?:the point )?${PT} (?:with|having|and|of|whose) (?:a )?(?:slope|gradient) (?:is |of |equal to |= ?)?(.+)$`),
      build: (m) => lineSlope(m[1], m[2], m[3], E) },
    { id: "line-slope", re: re(`^${LEAD}(?:equation (?:of|for) )?(?:the )?(?:straight )?line (?:with|having|of|whose) (?:a )?(?:slope|gradient) (?:is |of |equal to |= ?)?(.+?) (?:through|passing through|that passes through|containing|going through|and (?:through|passing through)) (?:the point )?${PT}$`),
      build: (m) => lineSlope(m[2], m[3], m[1], E) },
    { id: "line-slope", re: re(`^${LEAD}(?:equation (?:of|for) )?(?:the )?(?:straight )?line (?:with|having|of|whose) (?:a )?(?:slope|gradient) (?:is |of |equal to |= ?)?(.+?) and (?:a |whose |with )?y[- ]?intercept (?:is |of |equal to |at |= ?)?(.+)$`),
      build: (m) => lineSlope("0", m[2], m[1], E) },
  ];
}
const PT = String.raw`\(\s*([^,()]+?)\s*,\s*([^,()]+?)\s*\)`;
// a line from one point and a slope: hand the engine a second point one unit to the right
function lineSlope(x1, y1, s, E) {
  const a = E(x1), b = E(y1), k = E(s);
  if (!a || !b || !k || /[a-z=<>]/i.test((a + b + k).replace(/sqrt|pi/g, ""))) return null;
  return { math: `line(${a}, ${b}, (${a}) + 1, (${b}) + (${k}))`, goal: "line", interpretation: `line through (${a}, ${b}) with slope ${k}: it also passes through (${a} + 1, ${b} + ${k})` };
}

// Sentence tails that only restate the question ("... . find the numbers")
export const TAIL = /[.,]?\s*(?:find|what (?:are|is)|determine) (?:the|both) (?:two )?numbers?$/i;
