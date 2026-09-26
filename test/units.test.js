import { test, eq, ok, throws, rng } from "./harness.js";
import * as U from "../public/engine/units.js";
import * as N from "../public/engine/num.js";
import * as X from "../public/engine/expr.js";
import { toText } from "../public/engine/print.js";

const conv = (s) => U.convertText(s).text;
function message(fn) { try { fn(); } catch (e) { return e.message; } return null; }

test("units: parse unit expressions", () => {
  eq(U.parseUnit("km/h").text, "km/h");
  eq(U.parseUnit("m/s^2").text, "m/s^2");
  eq(U.parseUnit("kg*m^2/s^2").text, "kg*m^2/s^2");
  eq(U.parseUnit("J/(kg*K)").text, "J/(kg*K)");
  eq(U.parseUnit("m²").text, "m^2");
  eq(U.parseUnit("N m").text, "N*m");
  eq(U.parseUnit("s^-1").text, "s^-1");
  eq(U.parseUnit("m^(1/2)").text, "m^(1/2)");
  eq(U.dimensionName("m/s^2"), "acceleration");
  eq(U.dimensionName("kg*m/s^2"), "force");
  eq(U.dimensionName("J/(kg*K)"), "L^2 T^-2 Theta^-1");
  throws(() => U.parseUnit("furlongz"));
  throws(() => U.parseUnit("m^"));
});
test("units: prefixes", () => {
  eq(conv("1 km to m"), "1000 m");
  eq(conv("1 ms to s"), "1/1000 s");
  eq(conv("1 GW to kW"), "1000000 kW");
  eq(conv("1 µm to nm"), "1000 nm");
  eq(conv("1 mL to L"), "1/1000 L");
  eq(conv("1 MeV to keV"), "1000 keV");
});
test("units: exact conversions", () => {
  eq(conv("5 km/h to m/s"), "25/18 m/s");
  eq(conv("72 kph to m/s"), "20 m/s");
  eq(conv("60 mph to km/h"), "301752/3125 km/h");
  eq(conv("3 ft in cm"), "2286/25 cm");
  eq(conv("1 mi to ft"), "5280 ft");
  eq(conv("1 lb to oz"), "16 oz");
  eq(conv("1 kcal to J"), "4184 J");
  eq(conv("1 kWh to MJ"), "18/5 MJ");
  eq(conv("1 atm to Pa"), "101325 Pa");
  eq(conv("1 bar to atm"), "4000/4053 atm");
  eq(conv("90 deg to rad"), "pi/2 rad");
  eq(conv("1 gal to L"), "473176473/125000000 L");
  eq(conv("2 kg*m^2/s^2 to J"), "2 J");
  eq(conv("1 m/s^2 to km/h^2"), "12960 km/h^2");
});
test("units: affine temperatures in pure conversion", () => {
  eq(conv("100 degC to degF"), "212 degF");
  eq(conv("32 degF to degC"), "0 degC");
  eq(conv("-40 degC to degF"), "-40 degF");
  eq(conv("25 degC to K"), "5963/20 K");
  eq(U.convertText("32 degF to K").decimal, "273.15 K");
  eq(conv("0 K to degC"), "-5463/20 degC");
  // in a compound unit a degree Celsius is an interval
  eq(conv("1 J/(kg*degC) to J/(kg*K)"), "1 J/(kg*K)");
});
test("units: decimal display and repeating flag", () => {
  const r = U.convertText("5 km/h to m/s");
  eq(r.decimal, "1.388888888889 m/s");
  ok(r.repeating);
  eq(U.convertText("1 eV to J").decimal, "1.602176634e-19 J");
  eq(U.convertText("3 kg*m/s^2").text, "3 N");
});
test("units: adding meters and seconds throws a clear error", () => {
  const m = message(() => U.add(U.parseQuantity("3 m"), U.parseQuantity("2 s")));
  eq(m, "Quelvra: cannot add length (m) and time (s)");
  throws(() => U.sub("3 m", "2 kg"));
  eq(message(() => U.convert(U.parseQuantity("3 km"), "s")), "Quelvra: cannot convert length (km) to time (s)");
  throws(() => U.convert(U.parseQuantity("3 degC"), "m"));
});
test("units: arithmetic combines dimensions", () => {
  const a = U.add("3 m", "20 cm");
  eq(toText(a.value), "16/5"); eq(a.unit.text, "m");
  const v = U.div("10 m", "4 s");
  eq(toText(v.value), "5/2"); eq(v.unit.text, "m/s");
  const f = U.mul("2 kg", "3 m/s^2");
  eq(toText(f.value), "6"); eq(f.unit.text, "kg*m/s^2");
  eq(U.simplifyQuantity(f).unit.text, "N");
  const r = U.pow("4 m^2", "1/2");
  eq(toText(r.value), "2"); eq(r.unit.text, "m");
  const s = U.pow("2 m", 3);
  eq(toText(s.value), "8"); eq(s.unit.text, "m^3");
  throws(() => U.mul("3 degC", "2 m"));
  eq(U.sub("5 min", "30 s").unit.text, "min");
  eq(toText(U.sub("5 min", "30 s").value), "9/2");
});
test("units: simplify to named derived units", () => {
  eq(U.simplifyUnit("kg*m/s^2").text, "N");
  eq(U.simplifyUnit("g*m/s^2").text, "mN");
  eq(U.simplifyUnit("J/s").text, "W");
  eq(U.simplifyUnit("W/A").text, "V");
  eq(U.simplifyUnit("V/A").text, "ohm");
  eq(U.simplifyUnit("A*s").text, "C");
  eq(U.simplifyUnit("N/m^2").text, "Pa");
  eq(U.simplifyUnit("kg*m/s").text, "kg*m/s");
  const q = U.simplifyQuantity(U.parseQuantity("3 g*cm/s^2"));
  eq(q.unit.text, "N"); eq(toText(q.value), "3/100000");
});
test("units: dimensional analysis of equations", () => {
  ok(U.checkDimensions("F = m*a", { F: "N", m: "kg", a: "m/s^2" }).consistent);
  ok(U.checkDimensions("E = m*c^2", { E: "J", m: "kg", c: "m/s" }).consistent);
  const bad = U.checkDimensions("E = m*c", { E: "J", m: "kg", c: "m/s" });
  ok(!bad.consistent);
  eq(bad.problems[0], "the two sides differ: energy vs momentum");
  const sum = U.checkDimensions("x = v*t + a*t", { x: "m", v: "m/s", t: "s", a: "m/s^2" });
  eq(sum.problems[0], "cannot add length (v*t) and velocity (a*t)");
  ok(U.checkDimensions("x = x0 + v*t + a*t^2/2", { x: "m", x0: "m", v: "m/s", t: "s", a: "m/s^2" }).consistent);
  ok(!U.checkDimensions("y = sin(x)", { y: "1", x: "m" }).consistent);
  ok(U.checkDimensions("T = 2*pi*sqrt(L/g)", { T: "s", L: "m", g: "m/s^2" }).consistent);
  eq(U.checkDimensions("y = k*x", { y: "m" }).unknownSymbols.join(), "k,x");
});
test("units: parseQuantity forms", () => {
  eq(toText(U.parseQuantity("5 km/h").value), "5");
  eq(toText(U.parseQuantity("2.5e3 m").value), "2500");
  eq(toText(U.parseQuantity("1/3 h").value), "1/3");
  eq(toText(U.parseQuantity("3 x 10^8 m/s").value), "300000000");
  eq(U.parseQuantity("7").unit.text, "1");
  throws(() => U.parseQuantity("km"));
});

// ---------------- properties
const GROUPS = [
  ["m", "km", "cm", "mm", "in", "ft", "yd", "mi", "nmi", "angstrom"],
  ["g", "kg", "mg", "lb", "oz", "t", "ton"],
  ["s", "ms", "min", "h", "day", "week"],
  ["m/s", "km/h", "mph", "kph", "knot", "ft/s"],
  ["J", "kJ", "cal", "kcal", "eV", "Wh", "kWh", "N*m"],
  ["Pa", "kPa", "bar", "atm", "psi", "mmHg", "torr"],
  ["K", "degC", "degF"],
  ["m^3", "L", "mL", "gal", "in^3", "ft^3"],
  ["rad", "deg", "rev"],
];
test("property: unit round trips convert back exactly", () => {
  const r = rng(41);
  for (let i = 0; i < 300; i++) {
    const g = r.pick(GROUPS);
    const a = r.pick(g), b = r.pick(g);
    const v = N.Q(BigInt(r.int(-100000, 100000)), BigInt(r.int(1, 1000)));
    const q = U.quantity(X.num(v), a);
    const there = U.convert(q, b);
    const back = U.convert({ value: there.value, unit: there.unit }, a);
    ok(back.value === X.num(v), `${N.toString(v)} ${a} -> ${b} -> ${a}: ${toText(back.value)}`);
  }
});
test("property: conversion is linear for non-affine units and composes", () => {
  const r = rng(42);
  for (let i = 0; i < 150; i++) {
    const g = r.pick(GROUPS.filter((x) => x[0] !== "K"));
    const [a, b, c] = [r.pick(g), r.pick(g), r.pick(g)];
    const v = N.Q(BigInt(r.int(-1000, 1000)), BigInt(r.int(1, 50)));
    const direct = U.convert(U.quantity(X.num(v), a), c).value;
    const mid = U.convert(U.quantity(X.num(v), a), b);
    const via = U.convert({ value: mid.value, unit: mid.unit }, c).value;
    ok(direct === via, `${a} -> ${b} -> ${c}`);
  }
});
test("property: adding different dimensions always throws, same dimension never", () => {
  const r = rng(43);
  for (let i = 0; i < 200; i++) {
    const g1 = r.pick(GROUPS.filter((x) => x[0] !== "K")), g2 = r.pick(GROUPS.filter((x) => x[0] !== "K"));
    const a = U.quantity(r.int(1, 9), r.pick(g1)), b = U.quantity(r.int(1, 9), r.pick(g2));
    const same = U.sameDimension(a.unit, b.unit);
    let threw = false;
    try { U.add(a, b); } catch (e) { threw = true; eq(e.code, "DIMENSION"); }
    eq(threw, !same);
  }
});

test("units: long names, plurals and phrases", () => {
  const d = (s) => U.convertText(s).decimal;
  eq(d("5 km to miles"), "3.106855961187 mi");
  eq(d("5 kilometres to miles"), "3.106855961187 mi");
  eq(d("100 degrees fahrenheit to celsius").replace(/ .*/, ""), "37.777777777778");
  eq(d("30 degrees C to fahrenheit").replace(/ .*/, ""), "86");
  eq(d("60 miles per hour to meters per second"), "26.8224 m/s");
  eq(d("10 square feet to square meters"), "0.9290304 m^2");
  eq(d("2 pounds to kilograms"), "0.90718474 kg");
  eq(d("12 inches to feet"), "1 ft");
  eq(d("500 milliliters to liters"), "0.5 L");
  throws(() => U.convertText("5 bananas to miles"));
});
