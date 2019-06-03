var global = self;
// window is not accessible when we're a web worker, but haste uses it a lot.
// so, set the equivalent 'global', which haste also tries, to the equivalent 'self', which works
