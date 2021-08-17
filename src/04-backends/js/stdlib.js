// core JavaScript pervasives

class Call {
  constructor(op, continuation = x => x) {
    this.op = op;
    this.continuation = continuation;
  }

  perform(arg) {
    this.arg = arg;
    return this;
  }

  toString() {
    return `Call(op:'${this.op}', arg:'${JSON.stringify(this.arg)}')`;
  }
}

class HandlerClause {
  constructor(op, handler) {
    this.op = op;
    this.handler = handler;
  }

  toString() {
    return `HandlerClause(op:'${this.op}')`;
  }
}

class Handler {
  constructor(
    effectClauses = [],
    valueClause = x => x,
    finallyClause = x => x
  ) {
    this.effectClauses = effectClauses;
    this.finallyClause = finallyClause;
    this.valueClause = valueClause;
  }

  getEffectClause(result) {
    if (result instanceof Call) {
      return this.effectClauses
        .find(effectClause => effectClause.op === result.op);
    }
  }

  toString() {
    return `Handler(effectClauses: '${JSON.stringify(this.effectClauses.map(effectClause => effectClause.effect))}')`;
  }
}

const bind = function (result, continuation) {
  if (!(result instanceof Call)) {
    return continuation(result);
  }
  return new Call(
    result.op,
    y => bind(result.continuation(y), continuation)
  ).perform(result.arg);
}

const evalWithoutFinally = function (handler, result) {
  if (!(result instanceof Call)) {
    return handler.valueClause(result);
  }
  let effectClause = handler.getEffectClause(result);
  if (effectClause) {
    return effectClause.handler(
      result.arg,
      y => evalWithoutFinally(handler, result.continuation(y))
    );
  }
  return new Call(
    result.op,
    y => evalWithoutFinally(handler, result.continuation(y))
  ).perform(result.arg);
}

const eval = function (handler, result) {
  return bind(
    evalWithoutFinally(handler, result),
    handler.finallyClause
  );
}

const top_eval = function (result) {
  if (!(result instanceof Call)) {
    return result;
  }
  if (result.op === 'Print') {
    process.stdout.write(result.arg);
    return top_eval(result.continuation([]));
  }
  if (result.op === 'RandomInt') {
    const rnd = Math.floor(Math.random() * Math.floor(result.arg));
    return top_eval(result.continuation(rnd));
  }
  if (result.op === 'RandomFloat') {
    const rnd = Math.random() * result.arg;
    return top_eval(result.continuation(rnd));
  }
  if (result.op === 'Read') {
    const value = prompt("Enter value");
    return top_eval(result.continuation(value));
  }
  throw `Uncaught effect ${result.op} ${JSON.stringify(result.arg)}`;
}

const print = function (result) {
  process.stdout.write('- : ');
  console.dir(result, { depth: null });
}

class ArbitraryPattern {
  satisfies() {
    return true;
  }
}

class ConstantPattern {
  constructor(value) {
    this.value = value;
  }

  satisfies(value) {
    return this.value === value;
  }
}

class VariantPattern {
  constructor(value, shapes = []) {
    this.value = value;
    this.shapes = shapes;
  }

  satisfies(value) {
    return this.value === value.name
      && this.shapes.every(shape => shape.satisfies(value.arg));
  }
}

class TuplePattern {
  constructor(shapes = []) {
    this.shapes = shapes;
  }

  satisfies(value) {
    return this.shapes.length === Object.keys(value).length
      && this.shapes.every((s, i) => s.satisfies(value[i]));
  }
}

class RecordPattern {
  constructor(shapes = {}) {
    this.shapes = shapes;
  }

  satisfies(value) {
    return Object.keys(this.shapes).every(k => this.shapes[k].satisfies(value[k]));
  }
}
// end core JavaScript pervasives
