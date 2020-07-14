#ifndef ENCODING_H
#define ENCODING_H

#include <functional>

enum class EncodingType : int {
  Bit, Unit, List, NewType
};

struct Encoding {
  EncodingType type;
  int numChildren;
  const char* ident;
  int bit;
  std::function<Encoding*(int i)> childAt;
  int editable;
  std::function<void()> flipBit;
};

#endif
