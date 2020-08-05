#include "gui.h"

#pragma GCC diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#include <nana/gui.hpp>
#include <nana/gui/widgets/button.hpp>
#include <nana/gui/widgets/label.hpp>
#include <nana/gui/widgets/listbox.hpp>
#include <nana/gui/widgets/menubar.hpp>
#include <nana/gui/widgets/scroll.hpp>
#include <nana/paint/pixel_buffer.hpp>
#pragma GCC diagnostic pop

#include <cmath>
#include <gcem.hpp>
#include <memory>
#include <string>
#include <thread>

#include "createEncoding.hpp"
#include "draw.hpp"
#include "encoding.hpp"

#include "logo.xpm"

/*
      void OnAbout(wxCommandEvent& /unused/) {
        wxAboutDialogInfo info;
        info.AddDeveloper("Jonathan Tanner");
        info.SetIcon(wxICON(logo));
        info.SetLicence("None yet");
        info.SetName("Circuit");
        info.SetVersion("0.1.0");
        info.SetWebSite("https://github.com/nixCodeX/circuit");
        wxAboutBox(info);
      }
*/

namespace { // Unnamed namespace limits visibility to this translation unit
  struct Analytics { int size; int depth; };

  std::unique_ptr<GuiEncoding<nana::button>> inputGui;
  std::unique_ptr<GuiEncoding<nana::label>> outputGui;

  consteval auto drawLogo() -> Canvas<nana::pixel_color_t, 96, 96> {
    auto invis = nana::pixel_color_t{ .element = {0, 0, 0, 0} };
    auto black = nana::pixel_color_t{ .element = {0, 0, 0, 255} };
    auto grey = nana::pixel_color_t{ .element = {127, 127, 127, 255} };
    auto canvas = Canvas<nana::pixel_color_t, 96, 96>{invis, {48, 48}, -M_PI / 3.0};

    canvas.rectangle(-8, 8, -64, 64, grey, M_PI / 6.0);
    canvas.rectangle(-64, 0, -8, 8, grey);
    canvas.convexPolygon<5>({Point{0, -16}, {-16, -8}, {-16, 8}, {0, 16}}, grey);

    canvas.line({-16, -16}, {-16, 16}, 4, black); // Transistor
    canvas.line({-64,  0}, {-16, 0}, 4, black); // Base
    canvas.line({-16, -8}, {0, -16}, 4, black); // Collector 1
    canvas.line({0, -16}, {roundInt(48 * gcem::sin(M_PI / 6.0)), -16 - roundInt(48 * gcem::cos(M_PI / 6.0))}, 4, black); // Collector 2
    canvas.line({-16, 8}, {0, 16}, 4, black); // Emitter 1
    canvas.line({0, 16}, {-roundInt(48 * gcem::sin(M_PI / 6.0)), 16 + roundInt(48 * gcem::cos(M_PI / 6.0))}, 4, black); // Emitter 2

    return canvas;
  }

  void createWindow(char const* name, Encoding* input, Encoding* output, Analytics analytics) {
    auto form = nana::form{};
    form.caption(name);

    auto scrolling = nana::panel<false>{form};

    auto quitKey = nana::accel_key{'q'};
    quitKey.ctrl = true;
    form.keyboard_accelerator(quitKey, [&] () { form.close(); });

    auto menubar = nana::menubar{form};
    auto& fileMenu = menubar.push_back("File");
    fileMenu.append("Quit", [&] (auto&& /**/) { form.close(); });
    auto& helpMenu = menubar.push_back("Help");
    helpMenu.append
      ( "About"
      , [&] (auto&& /**/) {
          auto aboutbox = nana::form{form};
          aboutbox.caption("About");

          auto body = nana::panel<true>{aboutbox};
          body.bgcolor(nana::colors::white);

          auto constexpr logoCanvas = drawLogo();
          auto const logoBuf = logoCanvas.pixel_buffer();
          auto logo = nana::panel<true>{static_cast<nana::window>(body)};
          auto drawing = nana::drawing{logo};
          drawing.draw([&] (nana::paint::graphics& graphics) { logoBuf.paste(graphics.handle(), {0, 0}); });

          auto title = nana::label{body, "<size=20 bold>Circuit</>"};
          title.format(true);
          auto constexpr titleMargin = 25U;

          auto credit = nana::label{body, "Jonathan Tanner, 2020"};

          auto bodyLayout = nana::place{body};
          bodyLayout.div
            ( "<logo weight=96> "
              "< vert "
                "< title "
                  "margin=" + std::to_string(titleMargin) + " "
                  "weight=" + std::to_string(title.measure(0).height + 2 * titleMargin) + " "
                "> "
                "< credit "
                "> "
              "> "
            );
          bodyLayout["logo"] << logo;
          bodyLayout["title"] << title;
          bodyLayout["credit"] << credit;
          bodyLayout.collocate();
    
          auto ok = nana::button{aboutbox, "Ok"};
          ok.events().click([&] () { aboutbox.close(); });
          
          auto layout = nana::place{aboutbox};
          layout.div("vert<body><<><ok weight=75 margin=[10,5,15,0]> weight=50>");
          layout["body"] << body;
          layout["ok"] << ok;
          layout.collocate();
    
          aboutbox.show();
    
          aboutbox.modality();
        }
      );

    inputGui = std::make_unique<GuiEncoding<nana::button>>(scrolling, input);
    outputGui = std::make_unique<GuiEncoding<nana::label>>(scrolling, output);

    auto analyticsGui = nana::listbox(scrolling);
    analyticsGui.show_header(false);
    analyticsGui.enabled(false);
    analyticsGui.append_header("");
    analyticsGui.append_header("");
    analyticsGui.at(0).append({"Size:", std::to_string(analytics.size)});
    analyticsGui.at(0).append({"Depth:", std::to_string(analytics.depth)});

    auto graphics = nana::paint::graphics{{1, 1}};
    graphics.typeface(analyticsGui.typeface());
    auto analyticsHeight
      = (analyticsGui.size_item(0) + 1) * analyticsGui.scheme().item_height_ex
      + analyticsGui.size_item(0) * graphics.text_extent_size("SizeDepth").height
      ;

    auto scrollingLayout = nana::place{scrolling};
    scrollingLayout.div("vert<output><input><analytics weight=" + std::to_string(analyticsHeight) + ">");
    scrollingLayout["input"] << inputGui->handle();
    scrollingLayout["output"] << outputGui->handle();
    scrollingLayout["analytics"] << analyticsGui;
    scrollingLayout.collocate();

    auto scrollH = nana::scroll<false>{form};
    auto scrollV = nana::scroll<true>{form};
    auto corner = nana::panel<true>{form};

    auto scroll_value_changed = [&] () {
      scrolling.move
        ( static_cast<int>(-scrollH.value())
        , static_cast<int>(-scrollV.value())
        );
    };
    scrollH.events().value_changed(scroll_value_changed);
    scrollV.events().value_changed(scroll_value_changed);

    nana::place formLayout{form};
    formLayout.div("vert<menubar weight=28><<scrolling><scrollV weight=15>><scrollHBar <scrollH><corner weight=15> weight=15>");
    formLayout["menubar"] << menubar;
    formLayout["scrolling"] << scrolling;
    formLayout["scrollH"] << scrollH;
    formLayout["scrollV"] << scrollV;
    formLayout["corner"] << corner;
    formLayout.collocate();

    auto const minWidth = 50 * static_cast<unsigned int>(std::max(inputGui->width(), outputGui->width()));
    auto const minHeight = 300U;

    auto formResized = [&] (auto&& event) {
      if (event.width < minWidth) {
        scrollH.range(event.width * (minWidth - event.width) / minWidth);
        scrollH.amount(minWidth - event.width);
        scrolling.size({minWidth, scrolling.size().height});
      } else {
        scrollH.amount(0);
      }
      if (event.height < minHeight) {
        scrollV.range(event.height * (minHeight - event.height) / minHeight);
        scrollV.amount(minHeight - event.height);
        scrolling.size({scrolling.size().width, minHeight});
      } else {
        scrollV.amount(0);
      }
      formLayout.field_display("scrollHBar", event.width < minWidth);
      formLayout.field_display("scrollV", event.height < minHeight);
      formLayout.field_display("corner", event.height < minHeight);
    };
    form.events().resizing(formResized);
    form.events().resized(formResized);

    form.show();

    nana::exec();
  }
}

void gui(char const* name, Encoding* input, Encoding* output, int size, int depth) {
  Analytics analytics = {size, depth};

  (void)name;

  static bool isInitialised = false;
  if (isInitialised) {
    inputGui->update(input);
    outputGui->update(output);
  } else {
    isInitialised = true;
    createWindow(name, input, output, analytics);
  }
}

