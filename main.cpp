#include "range/v3/all.hpp"
#include <algorithm>
#include <cassert>
#include <fstream>
#include <functional>
#include <iostream>
#include <numeric>
#include <optional>
#include <random>
#include <unordered_map>
#include <vector>

using Player = int;
using Bid = std::pair<Player, int64_t>;
using Profile = std::unordered_map<Player, int64_t>;
using Evaluations = std::vector<int64_t>;

Evaluations random_evaluations(
    int64_t                 number_of_items,
    int64_t                 total_evaluation,
    std::optional<uint32_t> seed = std::nullopt)
{
   auto rng {
       seed.has_value() ? std::mt19937 {seed.value()}
                        : std::mt19937 {std::random_device {}()}};

   auto gen_evaluation = [&]() mutable
   {
      auto evaluation {
          std::uniform_int_distribution<int64_t> {0, total_evaluation}(rng)};
      total_evaluation -= evaluation;
      return evaluation;
   };
   Evaluations res {};
   res.reserve(number_of_items);
   ranges::generate_n(
       std::back_inserter(res),
       number_of_items - 1,
       gen_evaluation);
   res.push_back(total_evaluation);
   ranges::sort(res, std::greater<> {});
   return res;
}

class Game
{
 public:
   Game(int64_t number_of_players, int64_t number_of_items)
   {
      eval_matrix.reserve(number_of_players);
      std::generate_n(
          std::back_inserter(eval_matrix),
          number_of_players,
          [=]() { return random_evaluations(number_of_items, 50); });
   }

   const Evaluations& evaluations(Player player) const
   {
      return eval_matrix.at(player);
   }

   int64_t numberOfItems() const { return std::ssize(eval_matrix.at(0)); }
   int64_t numberOfPlayers() const { return std::ssize(eval_matrix); }

 private:
   std::vector<Evaluations> eval_matrix;
};

std::ostream& operator<<(std::ostream& o, const Game& game)
{
   o << "Player\tEvaluations\n";
   for (Player player : ranges::views::iota(0, game.numberOfPlayers()))
   {
      o << player << "     \t";
      for (auto evaluation : game.evaluations(player))
      {
         o << evaluation << '\t';
      }
      o << '\n';
   }
   return o;
}

template <typename ProfileView>
std::vector<Bid> bids_sorted_descending(ProfileView&& profile, const Game& game)
{
   using namespace ranges::views;

   auto total_bid_to_individual_items = [&](auto&& player_bid)
   {
      auto [player, number_of_bids] = player_bid;
      auto non_zero_bids = game.evaluations(player) | take(number_of_bids)
                         | transform(
                               [player](auto&& item_bid) {
                                  return Bid {player, item_bid};
                               });
      auto zero_bids =
          repeat_n(Bid {player, 0ll}, game.numberOfItems() - number_of_bids);
      return concat(non_zero_bids, zero_bids);
   };
   auto individual_item_bids =
       profile | transform(total_bid_to_individual_items) | join;

   auto res = individual_item_bids | ranges::to<std::vector>;
   ranges::sort(res, std::greater<> {}, &Bid::second);
   return res;
}

Profile all_zeroes(const Game& game)
{
   Profile res {};
   res.reserve(game.numberOfPlayers());
   auto i {0};
   ranges::generate_n(
       std::inserter(res, res.begin()),
       game.numberOfPlayers(),
       [&]() mutable {
          return Bid {i++, 0};
       });
   return res;
}

Profile all_evaluations(const Game& game)
{
   Profile res {};
   res.reserve(game.numberOfPlayers());
   auto i {0};
   ranges::generate_n(
       std::inserter(res, res.begin()),
       game.numberOfPlayers(),
       [&]() mutable {
          return Bid {i++, game.numberOfItems()};
       });
   return res;
}

Profile
random_plays(const Game& game, std::optional<uint32_t> seed = std::nullopt)
{
   Profile res {};
   res.reserve(game.numberOfPlayers());
   std::uniform_int_distribution<int64_t> bid_distribution {
       0,
       game.numberOfItems()};
   auto rng {
       seed.has_value() ? std::mt19937 {seed.value()}
                        : std::mt19937 {std::random_device {}()}};
   auto i {0};
   ranges::generate_n(
       std::inserter(res, res.begin()),
       game.numberOfPlayers(),
       [&]() mutable {
          return Bid {i++, bid_distribution(rng)};
       });
   return res;
}

template <typename ProfileView>
int64_t social_welfare(
    ProfileView&&         profile,
    const Game&           game,
    std::optional<Player> excluded = std::nullopt)
{
   // since in this game bids are either evaluations or zero, the social
   // welfare is the sum of winning bids
   auto all_bids_descending {bids_sorted_descending(profile, game)};
   auto exclude_if_player_excluded = [&excluded](auto&& bid)
   {
      return excluded.has_value() ? bid.first != excluded.value() : true;
   };
   auto k_highest_bids = all_bids_descending
                       | ranges::views::take(game.numberOfItems())
                       | ranges::views::filter(exclude_if_player_excluded);
   return ranges::accumulate(k_highest_bids, 0ll, std::plus<> {}, &Bid::second);
}

int64_t max_social_welfare_possible(const Game& game)
{
   // When every player plays their evaluations for all items, the k highest
   // ones win achieving maximum social welfare
   return social_welfare(all_evaluations(game), game);
}

int64_t payment(Player player, const Profile& profile, const Game& game)
{
   auto descending_bids {bids_sorted_descending(profile, game)};
   auto k_plus_one_highest_bid =
       (descending_bids.begin() + game.numberOfItems())->second;

   auto number_of_items_player_won {ranges::count(
       descending_bids | ranges::views::take(game.numberOfItems()),
       player,
       &Bid::first)};
   return number_of_items_player_won * k_plus_one_highest_bid;
}

int64_t vcg_payment(Player player, const Profile&, const Game& game)
{
   auto exclude_player = [player](auto&& bid)
   {
      return bid.first != player;
   };
   auto evaluations {all_evaluations(game)};
   auto evaluations_without_player =
       evaluations | ranges::views::filter(exclude_player);

   return social_welfare(evaluations_without_player, game, player)
        - social_welfare(evaluations, game, player);
}

template <typename ProfileView, typename PaymentFunction>
int64_t total_profits(
    ProfileView&&   profile,
    const Game&     game,
    PaymentFunction payment_fn)
{
   using namespace ranges::views;
   return ranges::accumulate(
       iota(0, game.numberOfPlayers())
           | transform([&](auto&& player)
                       { return payment_fn(player, profile, game); }),
       0ll);
}

template <typename ProfileView>
int64_t utility(Player player, ProfileView&& profile, const Game& game)
{
   auto all_bids_descending {bids_sorted_descending(profile, game)};
   auto k_plus_one_highest_bids =
       all_bids_descending | ranges::views::take(game.numberOfItems() + 1);

   auto k_plus_one_highest_bid {
       (k_plus_one_highest_bids.begin() + game.numberOfItems())->second};
   auto player_winning_bids =
       k_plus_one_highest_bids | ranges::views::take(game.numberOfItems())
       | ranges::views::filter([player](auto&& bid)
                               { return bid.first == player; });
   auto number_of_items_won {ranges::distance(
       player_winning_bids.begin(),
       player_winning_bids.end())};
   return ranges::accumulate(
              player_winning_bids,
              0ll,
              std::plus<> {},
              &Bid::second)
        - number_of_items_won * k_plus_one_highest_bid;
}

Profile best_response(Player player, Profile profile, const Game& game)
{
   using namespace ranges::views;

   auto max_utility_action {profile.at(player)};
   auto max_utility {utility(player, profile, game)};

   auto all_possible_actions {closed_iota(0, game.numberOfItems())};
   for (const auto new_action : all_possible_actions)
   {
      auto change_player_bid = [player, new_action](auto&& bid)
      {
         return bid.first == player ? Bid {player, new_action} : Bid {bid};
      };

      auto new_action_utility {
          utility(player, profile | transform(change_player_bid), game)};
      if (new_action_utility > max_utility)
      {
         max_utility_action = new_action;
         max_utility = new_action_utility;
      }
   }
   profile.at(player) = max_utility_action;
   return profile;
}

std::optional<Profile>
iterative_best_response(Profile initial_profile, const Game& game)
{
   Profile& current_profile {initial_profile};
   int      times_best_response_has_stayed_the_same {0};
   for (auto i : ranges::views::iota(
            0,
            (game.numberOfItems() + 1) * game.numberOfPlayers() + 1))
   {
      Player  current_player {i % game.numberOfPlayers()};
      Profile new_profile =
          best_response(current_player, current_profile, game);
      times_best_response_has_stayed_the_same =
          current_profile == new_profile
              ? times_best_response_has_stayed_the_same + 1
              : 0;

      if (times_best_response_has_stayed_the_same >= game.numberOfPlayers())
         return current_profile;

      current_profile = std::move(new_profile);
   }
   return std::nullopt;
}

std::ostream& operator<<(std::ostream& o, const Profile& profile)
{
   o << "Player\tNumber of bids\n";
   for (const auto& bid : profile)
   {
      o << bid.first << "     \t" << bid.second << '\n';
   }
   return o;
}

struct Ratio
{
   Ratio(int64_t enumerator, int64_t denominator)
       : enumerator {enumerator}
       , denominator {denominator}
   {
      assert(denominator != 0);
   }

   double value() const
   {
      return static_cast<double>(enumerator) / denominator;
   }

   int64_t enumerator;
   int64_t denominator;
};

std::ostream& operator<<(std::ostream& o, const Ratio& ratio)
{
   o << ratio.enumerator << '/' << ratio.denominator;
   return o;
}

struct Difference
{
   int64_t value() const { return lhs - rhs; }

   int64_t lhs;
   int64_t rhs;
};

std::ostream& operator<<(std::ostream& o, const Difference& diff)
{
   o << diff.lhs << '-' << diff.rhs;
   return o;
}

int main()
{
   using namespace ranges::views;

   struct Instance
   {
      Game       game;
      Profile    initial_profile;
      Ratio      sw_ratio;
      Difference profit_diff;
   };

   for (auto number_of_items : closed_iota(2, 15))
   {
      std::vector<Instance> instances {};
      instances.reserve(30000ll);

      std::cout << "k = " << number_of_items << '\n';
      for (auto i : closed_iota(1, 10000))
      {
         if (i % 100 == 0)
            std::cout << "Iteration: " << i << "\n";
         Game game {30, number_of_items};

         for (const auto& initial_profile :
              {all_zeroes(game), all_evaluations(game), random_plays(game)})
         {
            auto neq {iterative_best_response(initial_profile, game)};
            if (not neq.has_value())
            {
               std::cerr << "Game:\n" << game << '\n';
               std::cerr << "Initial profile:\n" << initial_profile << '\n';
               std::cerr << "Could not find Nash Equilibrium!\n";
            }
            else
            {
               Ratio sw_ratio {
                   max_social_welfare_possible(game),
                   social_welfare(neq.value(), game)};
               Difference profit_difference {
                   total_profits(neq.value(), game, &vcg_payment),
                   total_profits(neq.value(), game, &payment)};

               instances.push_back(
                   {game,
                    std::move(initial_profile),
                    std::move(sw_ratio),
                    std::move(profit_difference)});
            }
         }
      }

      auto sw_ratio_value_project = [](auto&& instance)
      {
         return instance.sw_ratio.value();
      };
      auto [min_ratio, max_ratio] {
          ranges::minmax(instances, {}, sw_ratio_value_project)};
      auto avg_ratio {
          ranges::accumulate(instances, 0.0, {}, sw_ratio_value_project)
          / instances.size()};

      auto profit_diff_value_project = [](auto&& instance)
      {
         return instance.profit_diff.value();
      };
      auto [min_diff, max_diff] {
          ranges::minmax(instances, {}, profit_diff_value_project)};
      auto avg_diff {
          ranges::accumulate(instances, 0.0, {}, profit_diff_value_project)
          / instances.size()};

      std::ofstream output_file {};
      output_file.open("output.txt", std::ios_base::app);

      for (auto* stream :
           std::initializer_list<std::ostream*> {&std::cout, &output_file})
      {
         *stream << "k = " << number_of_items << '\n' << '\n';
         *stream << "Average Social welfare ratio: " << avg_ratio << "\n\n";
         *stream << "Minimum Social Welfare ratio:" << min_ratio.sw_ratio
                 << ", achieved with\n"
                 << "Game:\n"
                 << min_ratio.game << "Initial Profile:\n"
                 << min_ratio.initial_profile << "\n\n";
         *stream << "Maximum social welfare ratio:" << max_ratio.sw_ratio
                 << ", achieved with\n"
                 << "Game:\n"
                 << max_ratio.game << "Initial Profile:\n"
                 << max_ratio.initial_profile << "\n\n";
         *stream << "Average vcg-auction profit difference: " << avg_diff
                 << '\n';
         *stream << "Minimum vcg-auction profit difference:"
                 << min_diff.profit_diff << ", achieved with\n"
                 << "Game:\n"
                 << min_diff.game << "Initial Profile:\n"
                 << min_diff.initial_profile << "\n\n";
         *stream << "Maximum vcg-auction profit difference:"
                 << max_diff.profit_diff << ", achieved with\n"
                 << "Game:\n"
                 << max_diff.game << "Initial Profile:\n"
                 << max_diff.initial_profile << "\n\n";
      }
      output_file.close();
   }

   return 0;
}