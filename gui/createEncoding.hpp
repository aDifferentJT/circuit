#ifndef CREATEENCODING_H
#define CREATEENCODING_H

#pragma GCC diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#include <nana/gui.hpp>
#include <nana/gui/widgets/group.hpp>
#pragma GCC diagnostic pop

#include <cassert>
#include <iostream>
#include <list>
#include <variant>

#include "encoding.hpp"

template<EncodingType type> class EncodingTypeTag {};

template<typename BitWidget>
class GuiEncoding;

class monostate {
  public:
    void update(Encoding*) { std::cerr << "Visiting monostate update" << std::endl; }

    auto handle() const -> nana::window {
      std::cerr << "Visiting monostate handle" << std::endl;
      return static_cast<nana::window>(nullptr);
    }

    auto width() const -> int {
      std::cerr << "Visiting monostate width" << std::endl;
      return 0;
    }
};

template<typename BitWidget>
class GuiEncodingList {
  private:
    nana::group group;
    std::list<GuiEncoding<BitWidget>> children{};
    int _width{0};

    void add_child(Encoding *encoding) {
      children.emplace_back(group, encoding);
      _width += children.back().width();
    }

    void collocate() {
      std::ostringstream div;
      div << "<children arrange=[";
      auto make_percentage = [this] (GuiEncoding<BitWidget>& x) { return static_cast<double>(x.width()) / static_cast<double>(this->width()) * 100; };
      if (!children.empty()) {
        div << make_percentage(children.front()) << "%";
        for (auto x = next(children.begin()); x != children.end(); x++) {
          div << "," << make_percentage(*x) << "%";
        }
      }
      div << "]>";
      group.div(div.str().c_str());
      for (auto&& x : children) {
        group["children"] << x.handle();
      }
      group.collocate();
    }

    GuiEncodingList(nana::window parent, char const *label = "") : group{parent, label} {}

  public:
    GuiEncodingList(nana::window parent, EncodingTypeTag<EncodingType::Unit>) : GuiEncodingList{parent} {}

    GuiEncodingList(nana::window parent, EncodingTypeTag<EncodingType::List>, Encoding *encoding)
      : GuiEncodingList{parent}
      {
        for (int i = 0; i < encoding->numChildren; i++) {
          add_child(encoding->childAt(i));
        }
        collocate();
      }

    GuiEncodingList(nana::window parent, EncodingTypeTag<EncodingType::NewType>, Encoding *encoding)
      : GuiEncodingList{parent, encoding->ident}
      {
        add_child(encoding->childAt(0));
        collocate();
      }

    void update(Encoding *encoding) {
      assert(encoding->type != EncodingType::Bit);
      int i = 0;
      for (auto& x : children) {
        x.update(encoding->childAt(i));
        i++;
      }
      assert(encoding->numChildren == i);
    }

    auto handle() const -> nana::window { return group.handle(); }

    auto width() const -> int { return _width; }
};

template<typename BitWidget>
class GuiEncodingBit {
  private:
    BitWidget bit;
  
  public:
    GuiEncodingBit(nana::window parent, EncodingTypeTag<EncodingType::Bit>, Encoding *encoding)
      : bit{parent, encoding->bit ? "1" : "0"}
      { if (encoding->editable) { bit.events().click(encoding->flipBit); } }

    void update(Encoding *encoding) {
      assert(encoding->type == EncodingType::Bit);
      bit.caption(encoding->bit ? "1" : "0");
    }

    auto handle() const -> nana::window { return bit.handle(); }

    auto width() const -> int { return 1; }
};

template<typename BitWidget>
class GuiEncoding {
  private:
    std::variant<monostate, GuiEncodingList<BitWidget>, GuiEncodingBit<BitWidget>> contents;
  public:
    GuiEncoding(nana::window parent, Encoding *encoding) {
      switch (encoding->type) {
        case EncodingType::Bit:
          contents.template emplace<GuiEncodingBit<BitWidget>>(parent, EncodingTypeTag<EncodingType::Bit>{}, encoding);
          break;
        case EncodingType::Unit:
          contents.template emplace<GuiEncodingList<BitWidget>>(parent, EncodingTypeTag<EncodingType::Unit>{});
          break;
        case EncodingType::List:
          contents.template emplace<GuiEncodingList<BitWidget>>(parent, EncodingTypeTag<EncodingType::List>{}, encoding);
          break;
        case EncodingType::NewType:
          contents.template emplace<GuiEncodingList<BitWidget>>(parent, EncodingTypeTag<EncodingType::NewType>{}, encoding);
          break;
      }
    }

    void update(Encoding *encoding) { std::visit([encoding] (auto &x) { x.update(encoding); }, contents); }
    auto handle() { return std::visit([] (const auto &x) { return x.handle(); }, contents); }
    auto width() { return std::visit([] (const auto &x) { return x.width(); }, contents); }
};

#endif
