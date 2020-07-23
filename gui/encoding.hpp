#ifndef ENCODING_H
#define ENCODING_H

#include <functional>

enum class EncodingType : int {
  Bit, Unit, List, NewType
};

struct Encoding {
  std::function<Encoding*(int i)> childAt;
  std::function<void()> flipBit;
  EncodingType type;
  int numChildren;
  const char* ident;
  bool bit;
  bool editable;
};

#endif
