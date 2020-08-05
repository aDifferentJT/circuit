#ifndef DRAW_H
#define DRAW_H

#include <nana/basic_types.hpp>

#include <array>
#include <cassert>
#include <gcem.hpp>
#include <gsl/gsl>

constexpr auto roundInt(auto x) -> int { return gsl::narrow_cast<int>(x + (x >= 0 ? 0.5 : -0.5)); }

struct Point {
  int x;
  int y;
};

namespace {
  template<typename To, typename From>
    constexpr auto safe_cast(From x) noexcept -> To {
      return x;
    }

  template<typename To, typename From>
    constexpr auto narrow(From from) noexcept -> std::optional<To> {
      auto to = static_cast<To>(from);
      if (static_cast<From>(to) != from) {
        return std::nullopt;
      } else if (!gsl::details::is_same_signedness<To, From>::value && ((to < To{}) != (from < From{}))) {
        return std::nullopt;
      } else {
        return to;
      }
    }

  static constexpr auto operator+(Point p1, Point p2) -> Point { return { p1.x + p2.x, p1.y + p2.y }; }
  static constexpr auto operator-(Point p1, Point p2) -> Point { return { p1.x - p2.x, p1.y - p2.y }; }
  static constexpr void operator+=(Point& p1, Point p2) { p1 = p1 + p2; }
  static constexpr void operator-=(Point& p1, Point p2) { p1 = p1 - p2; }

  consteval auto rotate(Point p, double angle) -> Point {
    if (angle == 0) { return p; }

    auto x = safe_cast<double, int>(p.x);
    auto y = safe_cast<double, int>(p.y);
    auto c = gcem::cos(angle);
    auto s = gcem::sin(angle);
    return
      { roundInt(x * c - y * s)
      , roundInt(x * s + y * c)
      };
  }
}

template<typename Pixel, std::size_t width, std::size_t height>
struct Canvas {
  private:
    std::array<std::array<Pixel, width>, height> buf;
  public:
    Point centre;
    double rotation{0.0};

    consteval Canvas(Pixel fill, Point _centre, double _rotation) : centre{_centre}, rotation{_rotation} {
      for (auto&& row : buf) { row.fill(fill); }
    }

    auto pixel_buffer() const {
      auto pixel_buffer = nana::paint::pixel_buffer{width, height};
      pixel_buffer.alpha_channel(true);
      pixel_buffer.put(reinterpret_cast<unsigned char const *>(buf[0].data()), width, height, 8 * sizeof(nana::pixel_color_t), sizeof(std::array<nana::pixel_color_t, width>), true);
      return pixel_buffer;
    }
  private:
    consteval void pixel(Point p, Pixel colour) {
      try {
        auto x = narrow<std::size_t>(p.x);
        auto y = narrow<std::size_t>(p.y);
        if (x && y) {
          if (*x < width && *y < height) {
            buf[*y][*x] = colour;
          }
        }
      } catch (std::out_of_range const &) {
      }
    }
  public:
    consteval void line(Point start, Point end, int thickness, Pixel colour) {
      start = rotate(start, rotation);
      end = rotate(end, rotation);
      start += centre;
      end += centre;
    
      auto direction = end - start;
      auto length = gcem::sqrt(direction.x * direction.x + direction.y * direction.y);

      auto minX = gcem::min(start.x, end.x);
      auto maxX = gcem::max(start.x, end.x);
      auto minY = gcem::min(start.y, end.y);
      auto maxY = gcem::max(start.y, end.y);
    
      if (gcem::abs(direction.x) >= gcem::abs(direction.y)) {
        auto m = safe_cast<double, int>(direction.y) / safe_cast<double, int>(direction.x);
        auto thicknessY = safe_cast<double, int>(thickness * gcem::abs(direction.x)) / length / 2.0;
        for (auto x = minX; x <= maxX; x++) {
          auto centreLine = m * safe_cast<double, int>(x - start.x) + start.y;
          for (auto y = roundInt(centreLine - thicknessY); y < roundInt(centreLine + thicknessY); y++) {
            pixel({x, y}, colour);
          }
        }
      } else {
        auto m = safe_cast<double, int>(direction.x) / safe_cast<double, int>(direction.y);
        auto thicknessX = safe_cast<double, int>(thickness * gcem::abs(direction.y)) / length / 2.0;
        for (auto y = minY; y <= maxY; y++) {
          auto centreLine = m * safe_cast<double, int>(y - start.y) + start.x;
          for (auto x = roundInt(centreLine - thicknessX); x < roundInt(centreLine + thicknessX); x++) {
            pixel({x, y}, colour);
          }
        }
      }
    }
  private:
    consteval void trapesium(int top, int bottom, int topLeft, int topRight, int bottomLeft, int bottomRight, Pixel colour) {
      auto mLeft = safe_cast<double, int>(bottomLeft - topLeft) / safe_cast<double, int>(bottom - top);
      auto mRight = safe_cast<double, int>(bottomRight - topRight) / safe_cast<double, int>(bottom - top);
      for (auto y = top; y <= bottom; y++) {
        auto xLeft = roundInt(mLeft * safe_cast<double, int>(y - top) + topLeft);
        auto xRight = roundInt(mRight * safe_cast<double, int>(y - top) + topRight);
        for (auto x = xLeft; x <= xRight; x++) {
          pixel({x, y}, colour);
        }
      }
    }
  public:
    template<std::size_t numVertices>
    consteval void convexPolygon(std::array<Point, numVertices> vertices, Pixel colour) {
      std::transform(vertices.begin(), vertices.end(), vertices.begin(), [&] (auto&& p) { return rotate(p, rotation) + centre; });

      std::sort(vertices.begin(), vertices.end(), [] (auto&& p1, auto&& p2) { return p1.y < p2.y; });

      auto centreLine = vertices.back() - vertices.front();
      auto mCentre = safe_cast<double, int>(centreLine.x) / safe_cast<double, int>(centreLine.y);

      std::array<bool, numVertices> onLeft;
      std::transform(vertices.begin(), vertices.end(), onLeft.begin(), [&] (auto&& p) { return p.x < mCentre * (p.y - vertices.front().y) + vertices.front().x; });

      auto findNextLeft = [&] (std::size_t i) { while (i < numVertices - 1 && !onLeft[i]) { i += 1; } return vertices[i]; };
      auto findNextRight = [&] (std::size_t i) { while (i < numVertices - 1 && onLeft[i]) { i += 1; } return vertices[i]; };

      auto top = vertices.front().y;
      auto topLeft = vertices.front().x;
      auto topRight = vertices.front().x;

      for (std::size_t i = 1; i < numVertices; i++) {
        auto bottom = vertices[i].y;

        int bottomLeft;
        int bottomRight;
        if (onLeft[i]) {
          bottomLeft = vertices[i].x;
          auto nextRight = findNextRight(i);
          auto m = safe_cast<double, int>(nextRight.x - topRight) / safe_cast<double, int>(nextRight.y - top);
          bottomRight = roundInt(m * safe_cast<double, int>(vertices[i].y - top)) + topRight;
        } else {
          bottomRight = vertices[i].x;
          auto nextLeft = findNextLeft(i);
          auto m = safe_cast<double, int>(nextLeft.x - topLeft) / safe_cast<double, int>(nextLeft.y - top);
          bottomLeft = roundInt(m * safe_cast<double, int>(vertices[i].y - top)) + topLeft;
        }

        trapesium(top, bottom, topLeft, topRight, bottomLeft, bottomRight, colour);

        top = bottom;
        topLeft = bottomLeft;
        topRight = bottomRight;
      }
    }

    consteval void rectangle(int left, int right, int top, int bottom, Pixel colour, double extraRotation = 0.0) {
      convexPolygon<4>
        ( { rotate({left, top}, extraRotation)
          , rotate({left, bottom}, extraRotation)
          , rotate({right, top}, extraRotation)
          , rotate({right, bottom}, extraRotation)
          }
        , colour
        );
    }
};

#endif
