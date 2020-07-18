#include "gui.h"

// wxWidgets "Hello world" Program
// For compilers that support precompilation, includes "wx/wx.h".
#include <wx/wxprec.h>
#ifndef WX_PRECOMP
#include <wx/wx.h>
#endif
#include <wx/aboutdlg.h>
#include <wx/collpane.h>
#include <wx/grid.h>

#include <string>

#include "createEncoding.hpp"

#include "logo.xpm"

std::string name;
Encoding* input = nullptr;
Encoding* output = nullptr;

struct { int size; int depth; } analytics;

class Panel : public wxScrolledWindow {
  public:
    wxSizer* sizer;

    Panel(wxWindow* parent, wxWindowID id) : wxScrolledWindow(parent, id) {
      wxCollapsiblePane* analyticsPane = new wxCollapsiblePane(this, wxID_ANY, "Analytics:");

      wxGrid* analyticsGrid = new wxGrid(analyticsPane->GetPane(), wxID_ANY);
      analyticsGrid->CreateGrid(2, 1, wxGrid::wxGridSelectRows);
      analyticsGrid->SetRowLabelValue(0, "Size:");
      analyticsGrid->SetCellValue(0, 0, std::to_string(analytics.size));
      analyticsGrid->SetRowLabelValue(1, "Depth:");
      analyticsGrid->SetCellValue(1, 0, std::to_string(analytics.depth));
      analyticsGrid->HideColLabels();
      analyticsGrid->EnableEditing(false);
      analyticsGrid->EnableDragRowSize(false);
      analyticsGrid->EnableDragColSize(false);
      analyticsGrid->Bind
        ( wxEVT_GRID_RANGE_SELECT
        , [analyticsGrid] (wxGridRangeSelectEvent& event) {
            if (analyticsGrid->IsSelection()) {
              analyticsGrid->ClearSelection();
            }
          }
        );

      wxSizer* analyticsSizer = new wxBoxSizer(wxVERTICAL);
      analyticsSizer->Add(analyticsGrid, wxSizerFlags().Proportion(0));
      analyticsPane->GetPane()->SetSizerAndFit(analyticsSizer);

      sizer = new wxBoxSizer(wxVERTICAL);

      sizer->Add(createEncoding(output, this), wxSizerFlags().Centre().Border());
      sizer->Add(createEncoding(input, this), wxSizerFlags().Centre().Border());
      sizer->Add(analyticsPane, wxSizerFlags().Proportion(0));

      SetSizerAndFit(sizer);
      sizer->FitInside(this);
      SetScrollRate(5, 5);
      SetMinSize(wxSize(100, 100));
    }
};

class Frame : public wxFrame {
  public:
    Panel* panel = new Panel(this, wxID_ANY);
    Frame(const wxString& title);
  private:
    void OnExit(wxCommandEvent& event) { Close(true); }
    void OnAbout(wxCommandEvent& event) {
      wxAboutDialogInfo info;
      info.AddDeveloper("Jonathan Tanner");
      info.SetIcon(wxICON(logo));
      info.SetLicence("None yet");
      info.SetName("Circuit");
      info.SetVersion("0.1.0");
      info.SetWebSite("https://github.com/nixCodeX/circuit");
      wxAboutBox(info);
    }
    wxDECLARE_EVENT_TABLE();
};

class App : public wxApp {
  public:
    Frame* frame;

    virtual bool OnInit() {
      frame = new Frame(name);
      frame->Show(true);
      return true;
    }
};

wxBEGIN_EVENT_TABLE(Frame, wxFrame)
  EVT_MENU(wxID_EXIT,  Frame::OnExit)
  EVT_MENU(wxID_ABOUT, Frame::OnAbout)
wxEND_EVENT_TABLE()

wxIMPLEMENT_APP_NO_MAIN(App);

Frame::Frame(const wxString& title)
  : wxFrame(nullptr, wxID_ANY, title)
{
  wxMenu *menuFile = new wxMenu; menuFile->Append(wxID_EXIT);
  wxMenu *menuHelp = new wxMenu; menuHelp->Append(wxID_ABOUT);

  wxMenuBar *menuBar = new wxMenuBar;
  menuBar->Append(menuFile, "&File");
  menuBar->Append(menuHelp, "&Help");
  SetMenuBar(menuBar);

  CreateStatusBar();

  wxSizer* sizer = new wxBoxSizer(wxVERTICAL);
  sizer->Add(panel, wxSizerFlags().Proportion(1).Expand());
  SetSizerAndFit(sizer);
}

void gui(const char* _name, Encoding* _input, Encoding* _output, int size, int depth) {
  name = _name;
  delete input;
  input = _input;
  delete output;
  output = _output;
  analytics = {size, depth};

  static bool isInitialised = false;
  if (isInitialised) {
    updateEncoding(wxGetApp().frame->panel->sizer->GetItem(static_cast<size_t>(0))->GetSizer(), output);
    updateEncoding(wxGetApp().frame->panel->sizer->GetItem(static_cast<size_t>(1))->GetSizer(), input);
  } else {
    isInitialised = true;
    int argc = 0;
    char* argv[0]{};
    wxEntry(argc, argv);
  }
}

